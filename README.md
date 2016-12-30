# Agda from Nothing: Order in the Types
A workshop for learning Agda with minimal prequisites.
The focus of this version of "[Agda from Nothing](https://github.com/scott-fleischman/agda-from-nothing)" is on creating correct-by-construction binary search trees.
The outline and code follows the paper *How to Keep Your Neighbours in Order* by Conor McBride (2014) [[PDF]](https://personal.cis.strath.ac.uk/conor.mcbride/Pivotal.pdf).

[![Build Status](https://travis-ci.org/scott-fleischman/agda-from-nothing-2017.svg?branch=master)](https://travis-ci.org/scott-fleischman/agda-from-nothing-2017)

## Installing Agda
This workshop uses Agda 2.5.2, though I expect code to work on older versions.

The official Agda installation instructions are [here](http://agda.readthedocs.io/en/latest/getting-started/installation.html).

On Mac, I like to do the following:
1. Install [stack](http://docs.haskellstack.org/en/stable/install_and_upgrade/#mac-os-x)
2. In a terminal run: `stack install --resolver nightly-2016-12-29 Agda`
3. Install [Aquamacs](http://aquamacs.org/)
4. In a terminal run: `agda-mode setup`
5. (Restart Aquamacs)

## Emacs Keybindings
See the [Agda docs](http://agda.readthedocs.io/en/latest/tools/emacs-mode.html) for all of the key bindings. Here are ones I commonly use. Note `C-` indicates holding the control key.

### Global (can be used anywhere)
* C-c C-l — Load file. I use this constantly.
* C-c C-f	— Move to next goal (**f**orward)
* C-c C-b — Move to previous goal (**b**ackwards)
* C-c C-d — Infer (**d**educe) type. Type in any expression and it infers the type.
* C-c C-n — Compute **n**ormal form. In other words, reduces the expression as much as possible.
* C-g — Quit what command sequence you started.

### In a hole/goal
* C-c C-c — Case split. Type in an argument name and it creates lines for each possible case. It works with multiple arguments.
* C-u C-c C-Comma — Show unnormalized goal type and context.
* C-u C-u C-c C-Comma — Show fully normalized goal type and context.
* C-c C-Space — Give (fill goal). Type checks the expression you typed in the hole, and if successful fills the hole.
* C-c C-r — Refine. Partial give: makes new holes for missing arguments.
  * If you've entered an expression in the hole, it will fill in the hole with that expression and make new holes for any missing arguments.
  * If you haven't entered anything in the hole, and if the hole is constrained to one constructor, it fills in the hole with that constructor and makes new holes for each of the constructor's arguments.
* C-c C-a — Automatic Proof Search (Auto). Tries to fill the hole with any solution. Note—this may not be a correct solution if the types aren't precise enough to constrain the term to only correct ones. Note also that it often fails to find a solution.
  * If you put `-l` in the hole, it will list the first 10 solutions it finds
  * If you put `-l -s 5` (or some other number) in the hole it will start at the 5th solution and list the next 10 solutions it finds.
  * If you only use `-s 5` it will fill the hole with the 5th solution.


### Resources
* [Agda Documentation](http://agda.readthedocs.io/)
* The old [Agda Wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Documentation) has links to other resources.
* Book: [Verified Functional Programming in Agda](http://www.amazon.com/Verified-Functional-Programming-Aaron-Stump/dp/1970001240) by Aaron Stump
