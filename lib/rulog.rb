require 'rubygems'

require 'singleton'
require 'ambit'
gem 'unific', '>=0.10'
require 'unific'

module Rulog
  VERSION = '0.9'

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
      e = Unific::Env.new # temporary fresh env for alpha renaming
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
    
    def trace lvl=false
      if lvl
        @trace = lvl
      else
        @trace = @trace + 1
      end
    end

    def untrace 
      @trace = 0
    end

    # takes a Rule
    def declare r
      raise unless r.kind_of? Rule  # XXX XXX alternately, we could coerce a functor to a fact
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
      amb.trace if @trace > 2
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
          # now put a new mark, so later cuts (and the unmark at the end of this scope) work
          amb.mark
          n_resolvent = resolvent
          n_x = x
        when ScopeMarker
          puts "finished rule" if @trace > 1
          amb.unmark!
          n_resolvent = resolvent
          n_x = x
        else
          puts "marking!" if @trace > 1
          amb.mark

          puts "choosing!" if @trace > 1
          rule = amb.choose(@p)
          puts "chose " + rule.to_s if @trace > 1

          amb.assert(e = Unific::unify(a, rule.head))
          n_resolvent = e.rename(e.instantiate(rule.conditions +
                                               [ ScopeMarker.instance ] +
                                               resolvent))
          n_x = e.instantiate(x)
        end
#       puts "resolvent: " + n_resolvent.inspect
        _solve amb, n_x, n_resolvent
      else
        x
      end
    rescue Ambit::ChoicesExhausted
      return false
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

  class DSLAdaptor
    def initialize
      # hash of variables seen with v
      @vars = {}

      # XXX XXX XXX this needs to be written
      # the idea here is to hide as many methods as we can get away with
      # so that we don't fail mysteriously if user uses their names as functor names.
    end

    def _
      Unific::Wildcard.instance
    end

    def v sym
      @vars[sym] ||= Unific::Var.new(sym)
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
