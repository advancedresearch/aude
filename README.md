
# Aude

An automated differentiation solver with a Lisp-like functional programming language

```text
=== Aude 0.2 ===
Type `help` for more information.
> mul

mul

ty: (fun (tup f64 f64) f64)

D: (lam (tup f64 f64) (tup mul($0) (lin_lam (tup f64 f64) add((tup mul((tup fst(f64)(f64)($0) fst(f64)(f64)($1))) mul((tup snd(f64)(f64)($0) snd(f64)(f64)($1))))))))
```

To run Aude from your Terminal, type:

`cargo install --example aude aude`

Then, to run:

`aude`

### References

[The Simple Essence of Automatic Differentiation](http://conal.net/papers/essence-of-ad/essence-of-ad-icfp.pdf)

### Design

Aude uses a Lisp-like syntax, to avoid pain during
translating to and from other programming languages.

For example, instead of `f64 -> f64`, Aude uses `(ty f64 f64)`.

Function application uses the syntax `<function>(<argument>)`,
e.g. `sin(0)`.

Variables uses [De Bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index),
e.g. `$0` refers to the lambda argument.

All operators take 2 arguments, e.g. `(fun f64 f64)`.

### Features

| Function | Description               |
| -------- | ------------------------- |
| add      | Addition                  |
| cos      | Cosine (trigonometry)     |
| fst      | First tuple component     |
| fst_par  | First parallel component  |
| id       | Identity                  |
| neg      | Negation                  |
| mul      | Multiplication            |
| sin      | Sine (trigonometry)       |
| snd      | Second tuple component    |
| snd_par  | Second parallel component |

| Op       | Description               | Example                         |
| -------- | ------------------------- | ------------------------------- |
| comp     | Composes functions        | `g . f = (comp g f)`            |
| lin_comp | Composes linear functions | `g . f = (lin_comp g f)`        |
| fun      | Function type             | `f64 -> f64 = (fun f64 f64)`    |
| lin      | Linear function type      | `f64 -o f64 = (lin f64 f64)`    |
| lam      | Lambda expression         | `\x:f64.x = (lam f64 $0)`       |
| lam_lin  | Linear lambda expression  | `\x:f64.x = (lin_lam f64 $0)`   |
| par      | Parallel tuple            | `f x g = (par f g)`             |
| tup      | Tuple                     | `(f, g) = (tup f g)`            |
| ty       | Type                      | `x : f64 = (ty x f64)`          |
