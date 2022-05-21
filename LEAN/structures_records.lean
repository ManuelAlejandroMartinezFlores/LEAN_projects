/- Declaring Structures -/

namespace decs
  --structure <name> <parameters> <parent-structures> where
  --  <constructor> :: <fields>


  structure Point (α : Type u) where 
    mk :: (x : α) (y : α)
    deriving Repr

  #check @Point.mk

  namespace Point 
    example (a b : α) : (mk a b).x = a := by rfl

    def add (p q : Point Nat) : Point Nat :=
      mk (p.x + q.x) (p.y + q.y)

    def smul (n : Nat) (p : Point Nat) : Point Nat :=
      mk (n * p.x) (n * p.y)

  end Point

end decs


/- Objects -/

namespace obj 

  structure Point (α : Type u) where 
    mk :: (x : α) (y : α)
    deriving Repr

  #check {x := 10, y := 20 : Point Nat}

  def p : Point Nat :=
    {x := 1, y := 2}

  structure Point3 (α : Type u) where 
    x : α 
    y : α 
    z : α 
    deriving Repr

  def q : Point3 Nat :=
    {x := 5, y := 5, z := 5}

  def r : Point3 Nat :=
    {p, q with x := 6}

  /-
  { x := 6, y := 2, z := 5 }
  -/
  #eval r

end obj


/- Inheritance -/

namespace Inheritance

  structure Point (α : Type u) where 
    mk :: (x : α) (y : α)
    deriving Repr

  inductive Color where
  | red | green | blue
  deriving Repr

  structure ColorPoint (α : Type u) extends Point α where
    c : Color
    deriving Repr

  def p : ColorPoint Nat :=
    {x := 1, y:= 2, c := Color.blue}

  /-
  { toPoint := { x := 1, y := 2 }, c := Inheritance.Color.blue }
  -/
  #eval p

end Inheritance