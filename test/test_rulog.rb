require 'rubygems'
require 'test/unit'
require 'unific'
require 'rulog'

class TestRulog < Test::Unit::TestCase
  def test_sanity
    Rulog::VERSION
  end

  def test_functors
    f1 = Rulog::Functor.new(:foo, 1, 2, 3)
    f2 = Rulog::Functor.new(:foo, 1, 2, 3)
    f3 = Rulog::Functor.new(:foo, 1, Unific::_, 3)
    f4 = Rulog::Functor.new(:foo, 1, Unific::Var.new, 3)

    f5 = Rulog::Functor.new(:bar, 1, 2, 3)
    f6 = Rulog::Functor.new(:foo, 2, 3, 4)
    f7 = Rulog::Functor.new(:foo, 1, 2)
    f8 = Rulog::Functor.new(:foo, 1, 2, 3, 4)

    assert Unific::unify f1, f1
    assert Unific::unify f1, f2
    assert Unific::unify f1, f3
    assert Unific::unify f1, f4

    assert !Unific::unify(f1, f5)
    assert !Unific::unify(f1, f6)
    assert !Unific::unify(f1, f7)
    assert !Unific::unify(f1, f8)
  end

  def test_rules
    vx = Unific::Var.new("x")
    vy = Unific::Var.new("y")
    vz = Unific::Var.new("z")

    f3 = Rulog::Functor.new :grandfather, vx, vy
    f4 = Rulog::Functor.new :father, vx, vz
    f5 = Rulog::Functor.new :father, vz, vy

    r1 = f3 [f4, f5]
    assert(r1.class == Rulog::Rule)
    assert(r1.head.f == f3.f)
  end

  def test_solve_simple
    rs1 = Rulog::RuleSet.new
    rs1.trace if ENV['RULOG_TRACE']
    f1 = Rulog::Functor.new :man, :adam
    r1 = Rulog::Rule.new f1  # fact -- no conditions

    rs1.declare r1

    v1 = Unific::Var.new("v1")
    q1 = Rulog::Functor.new :man, :adam
    q2 = Rulog::Functor.new :man, v1
    q3 = Rulog::Functor.new :man, :eve
    q4 = Rulog::Functor.new :woman, :adam

    assert rs1.solve q1
    assert rs1.solve q2
    assert !rs1.solve(q3)
    assert !rs1.solve(q4)
  end

  def test_solve_more
    rs1 = Rulog::RuleSet.new
    rs1.trace if ENV['RULOG_TRACE']

    f1 = Rulog::Functor.new :father, :abraham, :isaac
    f2 = Rulog::Functor.new :father, :isaac, :jacob
    r1 = Rulog::Rule.new f1 # fact -- no conditions
    r2 = Rulog::Rule.new f2 # fact -- no conditions

    vx = Unific::Var.new("x")
    vy = Unific::Var.new("y")
    vz = Unific::Var.new("z")

    f3 = Rulog::Functor.new :grandfather, vx, vy
    f4 = Rulog::Functor.new :father, vx, vz
    f5 = Rulog::Functor.new :father, vz, vy
    r3 = Rulog::Rule.new f3, f4, f5

    rs1.declare r1
    rs1.declare r2
    rs1.declare r3

    v4 = Unific::Var.new("v4")
    q1 = Rulog::Functor.new :grandfather, :abraham, v4

    sol = rs1.solve(q1)
    assert sol.f == :grandfather
    assert sol.args == [:abraham, :jacob]
  end

  def test_dsl
    f1 =  Rulog::declare { man(:abraham) }

    assert f1.class == Rulog::Functor
    assert f1 == Rulog::Functor.new(:man, :abraham)

    rs1 = Rulog::rules(
      Rulog::declare{ foo(v(:v1)) } [Rulog::declare {bar(v(:v1))}],
      f1 [ Rulog::declare{bar} ]
    )
    assert(rs1.class == Rulog::RuleSet)

    r2 = Rulog::declare {
      foo(v(:v1)) [bar(v(:v1)), baz(v(:v1))]
    }
    assert r2.class == Rulog::Rule
    assert r2.head.f == :foo

    # test method hiding -- turned off since not implemented yet
    # puts Rulog::declare { to_a }.class
    # puts Rulog::declare { clone }.class
    # puts Rulog::declare { man }.class
    # assert Rulog::declare { initialize } == Rulog::Functor.new(:initialize)
  end

  def test_solve_multi
    rs1 = Rulog::rules(Rulog::declare{  role(:joe, :employee)  },
                       Rulog::declare{  role(:joe, :parent)  },
                       Rulog::declare{  role(:bob, :employee)  })
    rs1.trace if ENV['RULOG_TRACE']

    assert rs1.solve_multi(Rulog::declare{  role(:joe, v(:role))  }).size == 2
    assert rs1.solve_multi(Rulog::declare{  role(:bob, v(:role))  }).size == 1
  end

  def test_classic_list
    rs1 = Rulog::rules(
                       Rulog::declare{ list(:nil)                             },
                       Rulog::declare{ list(cons(_, v(:xs))) [ list(v(:xs)) ] },

                       Rulog::declare{ len(:nil, 0)                           },
                       Rulog::declare{ len(cons(_, v(:v1)), s(v(:v2))) [ len(v(:v1), v(:v2)) ] },

                       Rulog::declare{ append(:nil, v(:xs), v(:xs))        },
                       Rulog::declare{ append(cons(v(:x), v(:xs1)), v(:xs2), cons(v(:x), v(:xs3))) [
                                               append(v(:xs1), v(:xs2), v(:xs3))]  }
                                                                      
                       )

    rs1.trace if ENV['RULOG_TRACE']

    assert rs1.solve(Rulog::declare{    list(:nil)             })
    assert rs1.solve(Rulog::declare{    list(cons(1, :nil))    })
    assert rs1.solve(Rulog::declare{    list(cons(2, cons(1, :nil)))    })
    assert !rs1.solve(Rulog::declare{   list(3)                })
    assert !rs1.solve(Rulog::declare{   list(cons(3, 2))       })

    assert rs1.solve(Rulog::declare{  list(v(:xs))                  })
    assert rs1.solve(Rulog::declare{  list(_)                       })
    assert rs1.solve(Rulog::declare{  list(cons(v(:x), :nil))       })
    assert rs1.solve(Rulog::declare{  list(cons(v(:x), v(:xs)))     })
    assert rs1.solve(Rulog::declare{  list(cons(v(:x), cons(v(:y), v(:ys))))  })

    assert rs1.solve(Rulog::declare{  len(:nil, 0)              })
    assert rs1.solve(Rulog::declare{  len(cons(1, :nil), s(0))  })

    assert rs1.solve(Rulog::declare{  len(cons(1, cons(2, :nil)), v(:xs))  })
    assert rs1.solve(Rulog::declare{  len(cons(1, cons(2, cons(3, :nil))), s(s(s(0))))   })

    assert rs1.solve(Rulog::declare{  append(:nil, cons(1,:nil), cons(1,:nil))    })
    assert rs1.solve(Rulog::declare{  append(v(:xs), cons(2,:nil), cons(1, cons(2,:nil)))    })
    assert rs1.solve(Rulog::declare{  append(cons(1,:nil), v(:xs), cons(1, cons(2,:nil)))    })
    assert rs1.solve(Rulog::declare{  append(cons(1,:nil), cons(2,:nil), v(:xs))    })
    assert rs1.solve(Rulog::declare{  append(v(:x), v(:xs), cons(1, cons(2, :nil)))    })
    assert rs1.solve(Rulog::declare{  append(v(:x), v(:xs1), v(:xs2))   })
    assert rs1.solve(Rulog::declare{  append(cons(1, cons(2, cons(3, :nil))),
                                             cons(4, cons(5, cons(6, :nil))), v(:xs))   })
  end

  def test_classic_peano
    rs1 = Rulog::rules(
                       Rulog::declare{  num(0)  },
                       Rulog::declare{  num(s(v(:x))) [ num(v(:x)) ]     },

                       Rulog::declare{  equal(0, 0)  },
                       Rulog::declare{  equal(s(v(:x)), s(v(:y))) [ equal(v(:x), v(:y)) ] },

                       Rulog::declare{  plus(v(:x), 0, v(:x)) },
                       Rulog::declare{  plus(v(:x), s(v(:y)), v(:z)) [
                                             plus(s(v(:x)), v(:y), v(:z)) ] }
                       )
    rs1.trace if ENV['RULOG_TRACE']

    assert rs1.solve(Rulog::declare{  num(0)    })
    assert rs1.solve(Rulog::declare{  num(s(s(s(0))))    })
    assert !rs1.solve(Rulog::declare{ num(s(s(s(1))))    })

    assert rs1.solve(Rulog::declare{  equal(0, 0)    })
    assert rs1.solve(Rulog::declare{  equal(s(s(s(0))), s(s(s(0))))    })
    assert !rs1.solve(Rulog::declare{ equal(s(s(s(0))), s(s(0)))    })

    assert rs1.solve(Rulog::declare{  plus(0, 0, 0)    })
    assert rs1.solve(Rulog::declare{  plus(s(s(0)), 0, s(s(0)))    })
    assert rs1.solve(Rulog::declare{  plus(s(s(0)), s(s(0)), s(s(s(s(0)))))    })
    assert !rs1.solve(Rulog::declare{ plus(s(s(0)), s(0), s(s(s(s(0)))))    })

    assert rs1.solve(Rulog::declare{  plus(0, v(:x), 0)    })
    assert rs1.solve(Rulog::declare{  plus(v(:x), 0, 0)    })
    assert rs1.solve(Rulog::declare{  plus(0, 0, v(:x))    })

    assert rs1.solve(Rulog::declare{  plus(s(s(0)), v(:x), s(s(0)))    })
    assert rs1.solve(Rulog::declare{  plus(s(s(0)), v(:x), s(s(s(0))))    })

    assert rs1.solve(Rulog::declare{  plus(s(s(0)), v(:x), s(s(0)))    })
    assert rs1.solve(Rulog::declare{  plus(v(:x), s(s(0)), s(s(s(0))))    })
    assert rs1.solve(Rulog::declare{  plus(v(:x), s(s(0)), s(s(0)))    })

    assert rs1.solve(Rulog::declare{  plus(s(s(0)), v(:x), s(s(s(s(0)))))    })
    assert rs1.solve(Rulog::declare{  plus(v(:x), s(s(0)), s(s(s(s(0)))))    })
    assert rs1.solve(Rulog::declare{  plus(v(:x), v(:y), s(s(s(s(0)))))    })
  end

  def test_hanoi
    # this cries out for a better enumerable unifier
    rs1 = Rulog::rules(
                       Rulog::declare{ append(:nil, v(:xs), v(:xs))      },
                       Rulog::declare{ append(cons(v(:x), v(:xs)), v(:ys), cons(v(:x), v(:zs))) [
                                               append(v(:xs), v(:ys), v(:zs))]  },

                       # returns steps to move stack on v1 to v2, using v3 as aux
                       Rulog::declare{ hanoi(s(0), v(:a), v(:b), v(:c), cons([v(:a), :to, v(:b)], :nil))  },
                       Rulog::declare{ hanoi(s(v(:n)), v(:a), v(:b), v(:c), v(:moves)) [
                                             hanoi(v(:n), v(:a), v(:c), v(:b), v(:ms1)),
                                             hanoi(v(:n), v(:c), v(:b), v(:a), v(:ms2)),
                                             append(v(:ms1), cons([v(:a), :to, v(:b)], v(:ms2)), v(:moves)) ]  }
                       )

    rs1.trace if ENV['RULOG_TRACE']

    assert rs1.solve(Rulog::declare{ append(cons(1, cons(2, cons(3, :nil))),
                                             cons(4, cons(5, cons(6, :nil))), v(:xs))   })
    
    # test a 3-disk stack
    assert rs1.solve(Rulog::declare{ hanoi(s(0), :a, :b, :c, v(:moves))   })
    assert rs1.solve(Rulog::declare{ hanoi(s(0), :a, :b, :c, cons([:a, :to, :b], :nil))   })
    assert rs1.solve(Rulog::declare{ hanoi(s(s(0)), :a, :b, :c, cons([:a, :to, :c], cons([:a, :to, :b], cons([:c, :to, :b], :nil))))   })

    # these currently diverge.  why?
    assert rs1.solve(Rulog::declare{ hanoi(s(s(0)), :a, :b, :c, v(:moves))   })
    assert rs1.solve(Rulog::declare{ hanoi(s(s(s(0))), :a, :b, :c, v(:moves))   })
  end

  def test_cut

    # from prolog cut example at
    # http://www.csupomona.edu/~jrfisher/www/prolog_tutorial/3_2.html
    # -- goal is to make 'unknown' a valid color only for parts not known as red or black
    # (without cuts, each red or black part could be used as its own color _or_ unknown
    # in a solution)
    #
    #	red(a).
    #   black(b).
    #	color(P,red) :- red(P),!.
    #	color(P,black) :- black(P),!.
    #	color(P,unknown). 
    #
    # this is a 'red' cut (pun stated as intended in the source material)

    rs1 = Rulog::rules( Rulog::declare { red(:a)   },
                        Rulog::declare { black(:b) },
                        Rulog::declare { color(v(:p), :red) [ red(v(:p)), cut! ]     },
                        Rulog::declare { color(v(:p), :black) [ black(v(:p)), cut! ] },
                        Rulog::declare { color(v(:p), :unknown) } )

    rs1.trace if ENV['RULOG_TRACE']

    # without the cut, these will return two answers for each
    # XXX XXX XXX (this is broken right now!
#    assert rs1.solve_multi(Rulog::declare{ color(:a, v(:col)) }).size == 1
#    assert rs1.solve_multi(Rulog::declare{ color(:b, v(:col)) }).size == 1

    assert rs1.solve(Rulog::declare{ color(:a, :red) })

    # this should always return just 'unknown'
    assert rs1.solve_multi(Rulog::declare{ color(:c, v(:col)) }).size == 1
  end

  # a test that cut works _and_ doesn't cut too much
  def test_cuts
    rs1 = Rulog::rules( Rulog::declare { red(:a)   },
                        Rulog::declare { color(v(:p), :red) [ red(v(:p)), cut! ]     },
                        Rulog::declare { color(v(:p), :unknown) } ,
                        Rulog::declare { finish(:a, :matte) },
                        Rulog::declare { finish(:a, :smooth) },
                        Rulog::declare { info(v(:x), v(:f), v(:c)) [
                                                                    finish(v(:x), v(:f)),
                                                                    color(v(:x), v(:c))
                                                                   ] })
    rs1.trace if ENV['RULOG_TRACE']

    # without working cut, this breaks
    # XXX XXX this is broken right now
#    assert rs1.solve_multi(Rulog::declare{ info(:a, v(:fin), v(:col)) }).size == 2
  end
end
