
class: middle, center

# scala .red[<3] math

@jeremyrsmith<br />
in/gentleman-and-a-scala

---

* Auto-differentiation
* Symbolic functions
* Linear algebra with massive data

---

# Auto-differentiation

--

Given a function `\(y = f(x)\)`, you evaluate `\(f(x + h)\)`.

--

Think of `\(h\)` as being kind of like `\(i\)`; it's not a real number. It's an
*infinitesimal* which has only the property that `\(h^2 = 0\)`.

--

The result of the evaluation will be `\(y + n*h\)`. And `\(n = \frac{\partial f}{\partial x}\)`.

---

# Polymorphic

This is a huge use case for parametric polymorphism.

--

If your function is polymorphic over, say, algebraic fields:

```scala
def f[A : Field](x: A): A = ??? 
```

--

Then you could define a data type to capture `x + h`, and define the `Field` for it.

---

# Spire

Spire already has typeclasses for `Group` & co.

--

It turns out they already have the data type for auto-diff as well. `Jet`.

--

So this was pretty easy. Just put a little bit of plumbing around `Jet`.

---

class: small-code

```scala
abstract class DifferentiableFunction[V[_]](implicit
 ds: DifferentiableSpace[V]
 ) {
 
  def apply[T : Eq : Field : NRoot : Trig](point: V[T]): T
  
  lazy val grad: GradientFunction[V] = new GradientFunction[V] {
    def apply[T : Eq : Field : NRoot : Trig](point: V[T]): V[T] =
      DifferentiableFunction.this.diff(point)
  }
  
  def diff[T : Eq : Field : NRoot : Trig](point: V[T]): V[T] = {
    ds.infs(apply(DifferentiableSpace[V].jets(point)))
  }
  
  def hessian[T : Eq : Field : NRoot : Trig](point: V[T]): V[V[T]] = {
    val result = apply(ds.jets(ds.jets(point)))
    ds.map(ds.fromArrayUnsafe(result.infinitesimal)) {
      j => ds.fromArrayUnsafe(j.infinitesimal)
    }
  }
}
```

---

You can use it by extending `DifferentiableFunction[V]` and providing `apply`...

--

For `V[_]` there are type aliases for homogeneous tuples, like `type V2[A] = (A, A)` etc.
 
Also `SizedArray` (statically sized array) for functions of > 22 variables.
   
--

But also there's a (possibly ill-advised) macro `Differentiable.apply`

---

```scala
val logistic = Differentiable {
  a => 1 / (1 + (-a).exp())
}

logistic(4.0)
logistic.grad(4.0) // also .grad.grad ad infinitum

// Multivariable for homogeneous tuples (V2 - V22)
// i.e. type V3[A] = (A, A, A)
val dist = Differentiable.over[V3] {
  case (x, y, z) => (x ** 2 + y ** 2 + z ** 2).sqrt()
}

// grad gives you V3 => V3 (tuple of partial derivatives)

// In this case returns V3[V3[Double]] (3-tuple of 3-tuples)
val h = dist.hessian(2.0, 3.0, 4.0)
```

---

# Problems

Spire's `Jet` is not sparse, so it can blow up when differentiating functions over many variables.

--

Its typeclass instances are also a single class, so deriving an instance is over-constrained.
You need

`T : Eq : Field : NRoot : Signed : Trig`
 
to get any instances for `Jet[T]`

--

It's not really performance-optimized.

---

# Symbolics

It might also be fun to define functions that are known *symbolically* at compile-time. This
turns out to be pretty easy, too:

```scala
sealed trait Placeholder[Expr] {
  def *[Lhs](
    that: Placeholder[Lhs]
  ): Placeholder[Multiply[Expr, Lhs]] = ???
  // etc  
}
```

The type parameter of `Placeholder` contains a recursive type describing the AST.

---

# Symbolics

```scala
trait SymbolicFunction[V[_], Expr]

object Symbolic {
  def apply[Expr](
    fn: Placeholder[Arg[0]] => Placeholder[Expr]
  ): SymbolicFunction[Id, Expr] = ???
  
  def apply[Expr](
    fn: (Ph[Arg[1]], Ph[Arg[2]]) => Ph[Expr]
  ): SymbolicFunction[V2, Expr] = ???
  
  //etc
}
```

The *type* of the result contains the entire AST.

---

```scala
val logistic = Symbolic {
  a => 1 / (1 + (-a).exp())
}
```

The type of `logistic` is:

```scala
SymbolicFunction[
    Id,
    Divide[
      LiteralInt[1],
      Add[
        LiteralInt[1],
        Exp[Negate[Arg[0]]]
      ]
    ]
]
```

---

# Symbolics

There are various ways you could evaluate a symbolic function...

--

You could literally build up an AST data structure (so `SymbolicFunction` has an instance of its `Expr` type) and
interpret that.

--

But since you have the whole AST at compile time as a type, you could also inline it at the call site with a macro.

--

(guess which one?)

---

But what about this?

```scala
def doSomething[Expr](fn: SymbolicFunction[V2, Expr]) =
    fn(1.0, 2.0)
```

--

Can't inline this, because `Expr` is abstract.

---

Middle ground: reify the AST in a macro-materialized typeclass, which you can pass around.

```scala
def doSomething[Expr : Evaluate](fn: SymbolicFunction[V2, Expr])
```

--

Reification occurs whenever `Expr` becomes concrete, and `Evaluate[Expr]` is materialized.

--

(Still at compile time)

---

# Aside

If you thought those `Expr` types are an insane idea...

--

```scala
def foo[A : Field, B : Field] = Template {
  (a: A, b: A) =>
    val foo = x + y
    bar.Module.someFn(foo)
}

TemplateFunction[
  (A @@ "x", B @@ "y") forSome { type A; type B; },
  Let[
    "foo", Invoke[Ident["x"], "+", Term["y"]],
    Invoke[bar.Module.type, "someFn", "foo"]
  ]
]
```

---

# Symbolic differentiation

There are also two ways you could differentiate it at compile time...

---

# Symbolic differentiation

You could do it with inductive proofs...

```scala
implicit def derivPow[
  ArgOrdinal <: Int, Exponent <: Int
](implicit dec: Decrement[Exponent]): Derivative.Aux[
  Pow[Arg[ArgOrdinal], Exponent],
  ArgOrdinal,
  Times[Exponent, Pow[Arg[ArgOrdinal], dec.Out]]
] = ???

// .. derivatives of other operations, and some inductions

implicit def derivConst[A, Arg <: Int]:
  Derivative.Aux[A, Arg, 0] = ???
```

---

Or you could differentiate in metaprogramming land.

--

Right now I'm marshaling the AST into a CAS (Symja) and differentiating there.

---

class: center, middle

# ooh-la-scala
## **O**bject-oriented **O**ff-**H**eap **L**inear **A**lgebra for Scala

Scala APIs backed by BLAS/LAPACK/MKL

---

# Problem

You can already use BLAS/MKL with **.red[netlib-java]**. It's used by Breeze and Spark (among others).
So why a new library?

--

Netlib-java uses Java arrays to back its data structures
* Can't have > 2 billion elements (maximum ~45k⨯45k matrix)
* Marshals to JNI = slow

--

Netlib-java is **.red[no longer maintained]** by the author.

---

# Ooh-la-scala

Ooh-la-scala keeps all data in off-heap memory allocations.

* Up to 2<sup>63</sup> elements
* Only pointers pass through JNI (cheap!)
* APIs make it seamless
* Can be memory-mapped to files

---

# 3 API levels

* Low-level: directly call BLAS/LAPACK functions by name
* Mid-level: data types for BLAS/LAPACK structures (vector, various matrices) with imperative APIs provided by typeclasses
* High-level: Expression-based, optimized at compile time

All three APIs strive to make allocation **.red[explicit]**, because we may be working with matrices that take a
significant portion of a machine's memory.

---

# Ooh-la-scala
## High-level code example

```scala
val a = Matrix[Double](1000, 1000)
val b = Vector[Double](1000)
// .. some code to fill in the matrix and vector

b := 2.0 * a * b
```

At compile time, it identifies that `b := 2.0 * a * b` optimizes to `GEMV(a, x = b, y = b, beta = 0, alpha = 2.0)`.
Because the target `b` can be assigned to the `GEMV` in/out argument `y`, it can skip a vector copy. 

---

class: center, middle

# Questions?