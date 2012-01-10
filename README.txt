= rulog

https://github.com/jimwise/ruby/tree/master/rulog

Author::    Jim Wise  (mailto:jwise@draga.com)
Copyright:: Copyright (c) 2011 Jim Wise
License::   2-clause BSD-Style (see LICENSE.txt)

== DESCRIPTION:

Rulog is Ruby Logic, a Logic Programming system for Ruby.

Rulog follows Prolog conventions where possible to do so within a Ruby DSL,
but makes a strong effort to retain a Rubyish "feel" wherever possible.  The
underlying functionality of Rulog, including the unification engine and
solver are also exposed directly through a set of Ruby classes.

While usable, this is a work in progress -- what's here now is a working
Logic Programming environment for Ruby, with integration with Ruby language
features (including unification of Prolog-style functors and Ruby scalar and
Enumerable types), along with a DSL to make these easier to use.  This is
sufficient for writing pure logic programs in Ruby, or for adding
logic-programming-based capabilities to a Ruby program.

Future releases will tighten the integration between this logic engine and
the rest of Ruby, including adding:

* the ability to escape to a Ruby block during unification, much as the "is"
  operator in Prolog allows direct use of mathematical operations at
  unification time

* the ability to include a predicate written in Ruby in a Rulog rule,
  similar to the use of FFI systems in modern prolog environments

* further improvements to the DSL used with Rulog#declare, to simplify use of
  these and other Rulog features

== REQUIREMENTS:

<b>Rulog depends on the ambit gem for backtracking.  Given this, Rulog will
not work in JRuby or MacRuby (no callcc).  It should work in Ruby 1.9 with
minor changes to ambit (callcc has moved to the 'continuation' stdlib).</b>

== INSTALL:

To install: 

    $ gem install rulog

== DEVELOPERS:

After checking out the source, run:

  $ rake newb

This task will install any missing dependencies, run the tests/specs,
and generate the RDoc.

== SYNOPSIS:

=== What is Logic Programming




== LICENSE:

(The MIT License)

Copyright (c) 2011 FIX

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
'Software'), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
