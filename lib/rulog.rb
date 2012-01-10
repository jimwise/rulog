require 'singleton'
require 'ambit'

module Rulog
  VERSION = '0.9.0'

  # Unification

  class Env
    @@trace = 0

    def initialize prev = {}
      @theta = prev.clone
    end

    def self.trace t=1
      @@trace = @@trace + t
    end

    def self.untrace t=1
      @@trace = @@trace - t
    end

    def fresh? x
      not @theta.has_key? x
    end

    def extend mappings
      Env.new @theta.update mappings.reject {|k, v| k.kind_of? Wildcard or v.kind_of? Wildcard }
    end

    def to_s
      "{ " + @theta.map{|k, v| "#{k} => #{v}"}.join(", ") + "} "
    end

    # returns either `false' or the MGU of the two terms, which can be
    #    a.) vars
    #    b.) wildcards
    #    c.) any ruby Enumerable, in which case unification recurs on the members
    #    d.) any other ruby object (as a ground term)
    #
    # this is a functional interface -- a new env is returned with the MGU, as taken
    # against the bindings already in this env
    def unify a, b
      puts "unifying #{a.to_s} and #{b.to_s}" if @@trace > 0

      # if either is already bound, substitute up front
      a = instantiate a
      b = instantiate b

      # any remaining Var is fresh.
      if a.kind_of? Var and b.kind_of? Var
          extend a => b
      elsif a.kind_of? Var
          extend a => b
      elsif b.kind_of? Var
          extend b => a
      elsif a.kind_of? Enumerable and b.kind_of? Enumerable
        return Rulog::fail unless a.size == b.size
        a.zip(b).inject(self) do |e, pair|
          e.unify(pair[0], pair[1]) or return Rulog::fail
        end
      else # both are ground terms
        if a == b
          self
        else
          Rulog::fail
        end
      end
    end

    # substitute any bound variables in an arbitrary expression, using traversal rules of traverse
    def instantiate s
      _traverse s do |v|
        if fresh? v
          v
        else
          instantiate @theta[v]
        end
      end
    end

    # alpha-rename an expression (all variables get new variables of same name.  useful, e.g. to give
    # each Rule its own private copy of all of its variables.
    def rename s
      _traverse s do |v|
        if fresh? v
          n = Rulog::Var.new(v.name)
          @theta[v] = n;
          n
        else
          instantiate @theta[v]
        end
      end
    end

    # helper for instantiate and rename
    # given an argument, if it is an:
    #   a.) var, replace it with the result of calling a block on it
    #   b.) enumerable, recur, instantiating it's members
    #   c.) any object, return it
    def _traverse s, &block
      case s
      when Rulog::Wildcard
        s
      when Var
        block.call(s)
      when Rulog::Functor # XXX XXX XXX messy -- this is the only place env knows of functor
        Rulog::Functor.new _traverse(s.f, &block), *_traverse(s.args, &block)
      when String
        # in ruby 1.8, strings are enumerable, but we want them to be ground
        s
      when Enumerable
        s.map {|x| _traverse(x, &block)}
      else
        s
      end
    end
  end

  def self.unify a, b, env = Env.new
    env.unify a, b
  end

  class Var
    attr_accessor :name

    def initialize name = "new_var"
      @name = name
      self.freeze
    end
    
    def to_s
      "?#{@name}"
    end
  end

  class Cut
    include Singleton
    
    def to_s
      "cut!"
    end
  end

  class ScopeMarker
    include Singleton
    
    def to_s
      "(scope marker)"
    end
  end

  class Wildcard < Var
    include Singleton

    def initialize
      super "_"
    end

    def to_s
      "_"
    end

    def == x
      true
    end
  end

  def self._
    Rulog::Wildcard.instance
  end

  def self.fail
    false
  end

  # for now, a functor is an enumerable which yields
  #    [ :functor, name, arg, arg, arg]
  # this allows unification to handle these (including considering arity)
  # without any new code.  That may change later, to make this less visible
  # to user, and to allow optimizations like indexing by functor and arity
  # for a large ruleset
  class Functor
    attr_accessor :f, :args
    include Enumerable

    def initialize f, *args
      @f = f
      @args = args
    end

    def each
      yield :functor
      yield @f
      @args.each {|a| yield a}
    end

    def arity
      @args.size
    end

    def size
      2 + arity
    end

    def to_s
      "#{@f}(#{@args.join(", ")})"
    end

    def == other
      if other.kind_of? Functor
        @f == other.f and @args == other.args
      else
        super.== other
      end
    end

    def [] *conditions
      Rulog::Rule.new(self, *conditions)
    end
  end

  class Rule
    attr_accessor :head, :conditions

    def initialize head, *conditions
      e = Rulog::Env.new # temporary fresh env for alpha renaming
      @head = e.rename(head)
      @conditions = e.rename(conditions)
    end

    def to_s
      "#{@head.to_s}#{@conditions.empty? ? '' : ' :- '}" + 
        "#{@conditions.map{|f| f.to_s}.join(', ')}."
    end

  end

  class RuleSet
    def initialize *rules
      @p = rules.map do |r|
        # make a functor the equivalent of a condition-less rule (ala prolog)
        case r
        when Rule
          r
        when Functor
          r[]
        end
      end
      @trace = 0
    end
    
    def trace t=1
      @trace = @trace + t
    end

    def untrace t=1
      @trace = @trace - t
    end

    # takes a Rule
    def declare r
      raise unless r.kind_of? Rule  # XXX XXX XXX for now
      @p << r
    end

    def to_s
      "\n    " + @p.join("\n    ") + "\n"
    end

    def solve goal
      answer = _solve Ambit::Generator.new, goal, [goal]
      puts "\ngoal:\n  #{goal}\nanswer:\n  #{answer or "no."}\n" if @trace > 0
      answer
    end

    # XXX XXX should take a max number of answers -- there are cases where we want
    # XXX XXX N of infinite answers
    def solve_multi goal
      answers = []
      amb = Ambit::Generator.new
      puts "\ngoal:\n  #{goal}\nanswer(s):\n" if @trace > 0

      answer = _solve amb, goal, [goal]
      if answer
        puts "  #{answer}\n" if @trace > 0
        answers << answer
        amb.fail!
      end
      puts "  no." if @trace > 0 and answers.size == 0
      answers
    rescue Ambit::ChoicesExhausted
      return answers
    end

    def _solve amb, x, resolvent = [x]
      if not resolvent.empty?
        a = resolvent.shift
        case a
        when Cut
          puts "cutting!" if @trace > 1
          amb.cut!
          n_resolvent = resolvent
          n_x = x
        when ScopeMarker
          puts "finished rule" if @trace > 1
          # ambit doesn't (yet!) give us a way to undo a mark operation
          # also, what happens if a rule has multiple cuts?  we need a scoped 
          # mark within ambit, perhaps?
          # amb.unmark!
          n_resolvent = resolvent
          n_x = x
        else
          # XXX XXX XXX cut should commit to the current choice of rule, not further.
          # XXX XXX XXX with this amb.mark commented out, cut! commits to all current
          # XXX XXX XXX choices, which is wrong.  but with this amb.mark commented in,
          # XXX XXX XXX cut does not commit far enough, which is worse

          # XXX XXX XXX the problem is that when we have a rule of the form
          # XXX XXX XXX   f(X) :- g(X), !.
          # XXX XXX XXX we make another choice or choices while proving g(X), and these
          # XXX XXX XXX get marked.
          #
          # XXX XXX XXX so we need a way to cut `to the right place' (read: back to just 
          # XXX XXX XXX before the choice of the current rule)
          #
          # puts "marking!" if @trace > 1
          # amb.mark

          puts "choosing!" if @trace > 1
          rule = amb.choose(@p)
          puts "chose " + rule.to_s if @trace > 1

          amb.assert(e = Rulog::unify(a, rule.head))
          resolvent.push ScopeMarker.instance
          n_resolvent = e.rename(e.instantiate(rule.conditions + resolvent))
          n_x = e.instantiate(x)
        end
        _solve amb, n_x, n_resolvent
      else
        x
      end
    rescue Ambit::ChoicesExhausted
      return false
    end
  end

  class DSLAdaptor
    def initialize
      # hash of variables seen with v
      @vars = {}

      # XXX XXX XXX this needs to be written
      # the idea here is to hide as many methods as we can get away with
      # so that we don't fail mysteriously if user uses their names as functor names.
    end

    def _
      Rulog::Wildcard.instance
    end

    def v sym
      @vars[sym] ||= Rulog::Var.new(sym)
      @vars[sym]
    end

    def cut!
      Rulog::Cut.instance
    end

    def method_missing sym, *args
      Rulog::Functor.new sym, *args
    end
   end

  def self.rules *rules
    Rulog::RuleSet.new(*rules)
  end

  def self.declare &block
    # this used to be a singleton, but we will soon want to keep variable state
    # across all uses of a name in a single declare...
    Rulog::DSLAdaptor.new.instance_eval(&block)
  end
end
