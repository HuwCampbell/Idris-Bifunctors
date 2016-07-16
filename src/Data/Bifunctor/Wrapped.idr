module Data.Bifunctor.Wrapped

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms

%access public export

||| Wrap a Bifunctor
|||
||| ````idris example
||| Wrap ("hello", 1)
||| ````
|||
record Wrapped (p : Type -> Type -> Type) a b where
  constructor Wrap
  unwrap : p a b

Bifunctor p => Bifunctor (Wrapped p) where
  bimap f g = Wrap . bimap f g . unwrap

Bifunctor p => Functor (Wrapped p a) where
  map f = Wrap . second f . unwrap

Biapply p => Biapply (Wrapped p) where
  (Wrap fg) <<.>> (Wrap xy) = Wrap (fg <<.>> xy)

Biapplicative p => Biapplicative (Wrapped p) where
  bipure a b                = Wrap $ bipure a b
  (Wrap fg) <<*>> (Wrap xy) = Wrap $ fg <<*>> xy

Bifoldable p => Bifoldable (Wrapped p) where
  bifoldMap f g = bifoldMap f g . unwrap

Bifoldable p => Foldable (Wrapped p a) where
  foldr f z = bifoldr (const $ const z) f z . unwrap

Bitraversable p => Bitraversable (Wrapped p) where
  bitraverse f g = map Wrap . bitraverse f g . unwrap

Bitraversable p => Traversable (Wrapped p a) where
  traverse f = map Wrap . bitraverse pure f . unwrap
