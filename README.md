# SiLemma

The goal of this project is to create an embedded hardware description language in Dafny.
I'm nowhere near that goal yet.

## Is that a sensible thing to try to do?

I have no idea.  Hoping trying to do it will answer that question.

## Is that a possible thing to do?

Again I have no idea.  Hoping trying to do it will answer that question.

## Why would you try to do that?

Verification is critical for hardware designs.  Being able to formally prove properties about circuits provides much stronger guarantees than testing.
However it's very hard to formally prove properties of an existing hardware design.  The idea is that if the verification is done together with
the circuit design it will make the process less painful.

## Why use dafny?

Dafny has an gentler learning curve than other proof assistants.

## How it is going?

It's a really slow process so far, since I'm mostly learning how to use proof assistants in general, and dafny in particular.
At the moment I'm still proving simple properties about directed graphs and mapping them onto a more realistic circuit model.
It'll be a long time before I'm actually doing anything useful with things that resemble real circuits, and there's a good
chance that I'll discover that this whole approach is not practical before then.

At the moment I'm just starting to be able to get things done in dafny, but still haven't worked out how to write nice code
and encapsulate things sensibly so that changing one thing doesn't wreck proofs everywhere else.

Optimisically, I'm a couple of years away from something useful.
