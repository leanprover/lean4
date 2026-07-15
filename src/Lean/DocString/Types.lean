/-
Copyright (c) 2023-2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module

prelude

public import Init.Data.Ord
import Init.Data.Nat.Compare
public import Init.Data.Array.GetLit

set_option linter.missingDocs true

namespace Lean.Doc

public section

/--
How to render mathematical content.
-/
inductive MathMode where
  /-- The math content is part of the text flow. -/
  | inline
  /-- The math content is set apart from the text flow, with more space. -/
  | display
deriving Repr, BEq, Hashable, Ord

/--
Inline content that is part of the text flow.
-/
inductive Inline (i : Type u) : Type u where
  /--
  Textual content.
  -/
  | text (string : String)
  /--
  Emphasis, typically rendered using italic text.
  -/
  | emph (content : Array (Inline i))
  /--
  Strong emphasis, typically rendered using bold text.
  -/
  | bold (content : Array (Inline i))
  /--
  Inline literal code, typically rendered in a monospace font.
  -/
  | code (string : String)
  /--
  Embedded TeX math, to be rendered by an engine such as TeX or KaTeX. The `mode` determines whether
  it is rendered in inline mode or display mode; even display-mode math is an inline element for
  purposes of document structure.
  -/
  | math (mode : MathMode) (string : String)
  /--
  A user's line break. These are typically ignored when rendering, but don't need to be.
  -/
  | linebreak (string : String)
  /--
  A link to some URL.
  -/
  | link (content : Array (Inline i)) (url : String)
  /--
  A footnote. In Verso's concrete syntax, their contents are specified elsewhere, but elaboration
  places the contents at the use site.
  -/
  | footnote (name : String) (content : Array (Inline i))
  /--
  An image. `alt` should be displayed if the image can't be shown.
  -/
  | image (alt : String) (url : String)
  /--
  A sequence of inline elements.
  -/
  | concat (content : Array (Inline i))
  /--
  A genre-specific inline element. `container` specifies what kind of element it is, and `content`
  specifies the contained elements.
  -/
  | other (container : i) (content : Array (Inline i))
deriving BEq, Ord, Repr, Inhabited

/-- Rewrites using a proof that two inline element types are equal. -/
def Inline.cast (inlines_eq : i = i') (x : Inline i) : Inline i' :=
  inlines_eq ▸ x

instance : Append (Inline i) where
  append
    | .concat #[], x => x
    | x, .concat #[] => x
    | .concat xs, .concat ys => .concat (xs ++ ys)
    | .concat xs, x => .concat (xs.push x)
    | x, .concat xs => .concat (#[x] ++ xs)
    | x, y => .concat #[x, y]

/-- No inline content. -/
def Inline.empty : Inline i := .concat #[]

/-- An item in either an ordered or unordered list. -/
structure ListItem (α : Type u) where
  /-- The contents of the list item. -/
  contents : Array α
deriving Repr, BEq, Ord, Inhabited

/-- An item in a description list. -/
structure DescItem (α : Type u) (β : Type v) where
  /-- The term being described. -/
  term : Array α
  /-- The description itself. -/
  desc : Array β
deriving Repr, BEq, Ord, Inhabited

/--
Block-level content in a document.
-/
inductive Block (i : Type u) (b : Type v) : Type (max u v) where
  /--
  A paragraph.
  -/
  | para (contents : Array (Inline i))
  /--
  A code block.
  -/
  | code (content : String)
  /--
  An unordered list.
  -/
  | ul (items : Array (ListItem (Block i b)))
  /--
  An ordered list.
  -/
  | ol (start : Int) (items : Array (ListItem (Block i b)))
  /--
  A description list that associates explanatory text with shorter items.
  -/
  | dl (items : Array (DescItem (Inline i) (Block i b)))
  /--
  A quotation.
  -/
  | blockquote (items : Array (Block i b))
  /--
  Multiple blocks, merged.
  -/
  | concat (content : Array (Block i b))
  /--
  A genre-specific block. `container` specifies what kind of block it is, while `content` specifies
  the content within the block.
  -/
  | other (container : b) (content : Array (Block i b))
deriving BEq, Ord, Repr, Inhabited

/-- An empty block with no content. -/
def Block.empty : Block i b := .concat #[]

/-- Rewrites using proofs that two inline element types and two block types are equal. -/
def Block.cast (inlines_eq : i = i') (blocks_eq : b = b') (x : Block i b) : Block i' b' :=
  inlines_eq ▸ blocks_eq ▸ x

/--
A logical division of a document.
-/
structure Part (i : Type u) (b : Type v) (p : Type w) : Type (max u v w) where
  /-- The part's title -/
  title : Array (Inline i)
  /--
  A string approximation of the part's title, for use in contexts where formatted text is invalid.
  -/
  titleString : String
  /-- Genre-specific metadata -/
  metadata : Option p
  /-- The part's textual content -/
  content : Array (Block i b)
  /-- Sub-parts (e.g. subsections of a section, sections of a chapter) -/
  subParts : Array (Part i b p)
deriving BEq, Ord, Repr, Inhabited

/-- Rewrites using proofs that inline element types, block types, and metadata types are equal. -/
def Part.cast (inlines_eq : i = i') (blocks_eq : b = b') (metadata_eq : p = p')
    (x : Part i b p) : Part i' b' p' :=
  inlines_eq ▸ blocks_eq ▸ metadata_eq ▸ x
