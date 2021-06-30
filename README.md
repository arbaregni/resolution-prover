# resolution-prover

Uses [propositional resolution](http://intrologic.stanford.edu/chapters/chapter_05.html) to prove statements and proofs on discord.
Note that this is [very different than being true or not](#provability).

## Table of contents

- [resolution-prover](#resolution-prover)
  - [Tutorial](#tutorial)
    - [Identifiers](#ident)
    - [Functions (Predicates)](#fun)
    - [Synonyms for Logical Connectors](#synonyms)
    - [Binding Strength](#binding)
    - [Negation](#not)
    - [Disjunction - Or](#or)
    - [Conjunction - And](#and)
    - [Implication - If](#if)
    - [Biconditional - If and Only If](#iff)
    - [Exclusive Or - xor](#fol)
    - [Quantification and First Order Logic](#fol)
      - [Universal Quantification - forall](#universal)
      - [Existential Quantification - exists](#existential)
   - [Provability and Truth](#provability)
      
      
[Made with markdown-toc](https://luciopaiva.com/markdown-toc/)

## <a name="tutorial"></a> Tutorial

For a presentation of the grammar used by the parser, see [grammar.pest](grammar.pest). The following is a look into the specific syntax [resolution-prover](https://github.com/arbaregni/resolution-prover/) uses, as well as an introduction to formal logic.

### <a name="ident"></a> Identifiers
Identifiers can be any alphanumeric characters (any case), including as well hyphens (-) and underscores (\_).
On their own, identifiers correspond to constants. For instances, writing
```
heron
```
proposes a constant, and ***<ins>calls</ins>*** it `heron`. Mathematics doesn't "know" anything about herons, we're just referencing an abstract mathematical entity by the name `heron`.
The things we assume about this entity are what makes it "act" logically like we would expect a bird of this sort to.

The name `heron` shouldn't mislead you into believing that this abstraction behaves like a heron you might be used to. That being said, the names in this document are chosen suggestively to illustrate a point.

***DO NOT BE FOOLED. NAMES ARE ARBITRARY AND HAVE NO MEANING BEYOND ASSUMPTIONS YOU MAKE ABOUT THEM.***

Identifiers can also be made into variables by [quantifying](#fol) over them.

### <a name="fun"></a> Functions (Predicates)
An identifier followed by a parenthesized argument list, like so:
```
IsBird(heron)
```
now, `IsBird` is a function with one argument.

You can also define functions with more than one argument:
```
Eats(fish, heron)
```

You can nest functions:
```
Eats(ChildrenOf(fish), heron)
```

Functions with different arities (numbers of arguments) are distinct. For instance,
```
P(a)
```
has no logical relationship with
```
P(a, b)
```

For now, you can define functions with zero arguments (`P()`).
Since constants are actually implemented as functions with zero arguments, this will eventually no longer be the case.

Functions/predicates don't inherit meaning from their names, just like simple constants don't.

### <a name="synonyms"></a> Synonyms for Logical Connectors
There are several interchangeable symbols for each connective.
You can use whatever you like.
| Logical Connective         | Synonyms                      |
|----------------------------|-------------------------------|
| negation                   | not, !, ~                     |
| disjunction                | or, \|\|, \|, ∨, \\/          |
| conjunction                | and, &&, &, ∧, /\\            |
| implication                | implies, =>, ->, ==>, -->     |
| biconditional              | iff, <=>, <->, <==>, <-->     |
| exclusive or               | xor                           |
| universal quantification   | forall, ∀                     |
| existential quantification | exists, ∃                     |


### <a name="binding"></a> Binding Strength
Here is a quick summary of the binding strength:

| Logical Connectives        | Binding Strength |
|----------------------------|------------------|
| negation                   | strongest        |
| and, or, if, iff, xor      | medium           |
| forall, exists quantifiers | weakest          |

For instance,
```
not a or b
```
means
```
(not a) or (b)
```

because the `not` binds more tightly to the `a` than the `or` does.

Likewise, 
```
forall x: x or ~x
```
means
```
( forall x: (x or ~x) )
```
because the `or` binds more tightly to the `x` than the `forall x:` does. See [quantification](#fol) for more details. This might be surprising, but it was marginally easier to implement, so :man_shrugging:.

When mixing `and`, `or`, `iff`, and `xor`, parenthesis are **required** to make your meaning clear.
For instance,
```
a or b and c
```
will produce an error. Write
```
(a or b) and c
```
or
```
a or (b and c)
```
instead.


### <a name="not"></a> Negation
If `heron` is true, then `not heron` is false, and vice versa.

### <a name="or"></a> Disjunction - Or
You can chain as many expressions together with `or` as you like:
```
heron or parrot or owl or hawk or osprey
```
This expression is true when *at least one* sub expression is true. You don't need parenthesis if it's just `or`s, because `or` is [associative](https://en.wikipedia.org/wiki/Associative_property).
To paraphrase Professor Matthew Macauley, parenthesis are permitted anywhere, but required nowhwere.

In simplest case, we can construct a table to represent all the possibilities:

    `p or q`
|      | `~p`  | `p`  |
|------|-------|------|
| `~q` | false | TRUE |
| `q`  | TRUE  | TRUE |

The cell on the top left should be read as `p or q` has the truth value TRUE when `p` is TRUE and `q` is false.

### <a name="and"></a> Conjunction - And
Like or, `and` is [associative](https://en.wikipedia.org/wiki/Associative_property), so we can write it as many times as we like without parenthesis:
```
salmon and trout and bass and sunfish
```
This expression is true if *all* sub expressions are true. In this simplest case, we can construct a truth table:
        `p and q`
|      | `~p`   | `p`   |
|------|--------|-------|
| `~q` | false  | false |
| `q`  | false  | TRUE  |

### <a name="if"></a> Implication - If
You can not chain `implies`:
```
heron implies bird
```
This is often a particularly hard expression to intuit. The proposition `bird implies heron` ***HAS A TRUTH VALUE***, just like everything else we've seen.
It can be false. In fact, there is exactly one case in which this is false: when `bird` is true, but `heron` is not.
What we have just said is that `not (bird implies heron)` is logically equivalent to `bird and not heron`.

    `bird implies heron`
|        | ~bird | bird  |
|--------|-------|-------|
| ~heron | TRUE  | false |
| heron  | TRUE  | TRUE  |

Notice that `bird implies heron` is TRUE when `bird` is false. This makes [perfect sense](https://en.wikipedia.org/wiki/Vacuous_truth), even if you don't realize it.
Consider the sentence "all of the heron's iPhones are charged". This is vacuously true because herons don't own iPhones (as of 2020). 

If this isn't the relationship you want to capture, you might want a [biconditional](#iff);

### <a name="iff"></a> Biconditional - If and Only If
Although if and only if (iff) is associative, its behavior is non-intuitive so you can not chain them as to prevent confusion:
```
great-blue-heron iff ardea-herodias
```
This is true when `great-blue-heron` and `ardea-herodias` have the same truth value.
This is the same as saying that `great-blue-heron implies ardea-herodias` and `ardea-herodias implies great-blue-heron`. Hence the "bi-" in "biconditional".

   `p iff q`
|    | ~p    | p     |
|----|-------|-------|
| ~q | TRUE  | false |
| q  | false | TRUE  |

### <a name="xor"></a> Exclusive Or - xor
Like [iff](#iff), exclusive or (xor) is associative, but its behavior is non-intuitive so chaining is forbidden to prevent confusion.
```
hot xor cold
```
This is true when `hot` and `cold` have opposite truth values.
   `p xor q`
|    | ~p    | p     |
|----|-------|-------|
| ~q | false | TRUE  |
| q  | TRUE  | false |

### <a name="fol"></a> Quantification and First Order Logic
Whereas predicate calculus and zeroth-order logic deal with concrete specifics, [first order logic](https://en.wikipedia.org/wiki/First-order_logic) can deal with an infinity of them.
As such, it is a much more [powerful system](https://en.wikipedia.org/wiki/G%C3%B6del%27s_speed-up_theorem).

It does this by introducing quantifiers. These take an identifier name and "quantify" over it, turning it into a variable:
```
forall x: P(x)
```
```
exists x: Q(x)
```

In the context of the `forall x:` and `exists x:` expressions, `x` is a variable, and not a constant. Quantifiers ***must*** be followed by exactly 1 identifier to quantify over. Anything else is erroneous nonsense.

The name exists as a variable only in the context of the quantified expression. For instance,
```
( exists x: Quacks(x) ) => Quacks(x)
```
is not provable.
```
 ( exists x: Quacks(x) ) => Quacks(x)
             ^^^^^^^^       ^^^^^^^^^
         variable $x        constant x
```
In the quantified expression, `x` is a variable. It is not the same as the `x` in the other expession, which is a constant. Renaming things makes it more clear what's happening:
```
 ( exists x: Quacks(x) ) => Quacks(xerxes)
```
The existence (or lack thereof) of something that quacks has nothing to do with something called `xerxes` quacking. See [existential quantification](#existential).
      

The following are not the only quantifiers, but they are traditional and enough for most purposes.

#### <a name="universal"></a>Universal Quantification - forall
The [universal quantifier](https://en.wikipedia.org/wiki/Universal_quantification) means that its variable may be replaced by *anything and everything*. For instance,
```
forall x: Bird(x)
```
implies `Bird(heron)`, `Bird(fish)`, `Bird(happy)`, `Bird(you)`, `Bird(the-strange-ability-present-in-some-individuals)`, `Bird(Powerset(apple))`, `Bird(x)`, `Bird(AnyThingBut(x, y, z))`, etc. You get the picture. Intuitively, this could be understood to mean "all things which are called birds".

Since that quickly obviates the need to call anything a bird, we might state instead
```
forall x: Bird(x) => Flies(x)
```
This means that all things that are called birds, are also called flying things. Intuitively, we might take this to be the proposition stating that "all birds fly".

#### <a name="existential"></a>Existential Quantification - exists
The [existential quantifier](https://en.wikipedia.org/wiki/Existential_quantification) means there is *at least one* specific object that we may substitute into it.
```
exists x: Bird(x)
```
Means that there is at least one thing such that `Bird` of that thing is a true expression. Intuitively, "birds exist". A [controversial](https://www.youtube.com/watch?v=zNtr0RahRqM) proposition, I know.

This does not say anything *about* the bird(s) that exist(s). There number of them could be 1, 27720, or infinite. This proposition states only that that number is **NOT** zero. From this proposition, we derive nothing about what these birds that (supposedly) exist are. They *could* be robotic.

## <a name="provability"></a> Provability and Truth

When asked to **prove** the following, we find:

`IsBlue(the-sky)` :x:

even though the sky is blue. This is because we don't care about seeing of a proposition is true, just if it is provable. And `IsBlue(the-sky)` is not nessicarily true with no prior assumptions. In general, it is much easier to define proofs than truths. See [Gödel's incompleteness theorems](https://en.wikipedia.org/wiki/G%C3%B6del%27s_incompleteness_theorems) and [Tarki's undefinability theorem](https://en.wikipedia.org/wiki/Tarski%27s_undefinability_theorem).

To be precise, reacting with :x: means that no proof exists, and :white_check_mark: means that a proof exists.

