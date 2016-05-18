# translation-mod
A coq plugin implementing the translation associated to a modality

Let ◯ be a strict modality.

To explain the translation on positive types as well, we also translate the sum type *A + B*, with associated constructors *in*<sub>ℓ</sub> and *in*<sub>*r*</sub> and eliminator ⟨\_,\_⟩. We note *J* the eliminator of the identity type.

-   For types (assuming *A ≠ Type*)  
  -  *[Type] ≔ (Type<sup>◯</sup> ; π<sub>Type<sup>◯</sup></sub>)*
  -  We introduce the notation *⟦A⟧ ≔ π<sub>1</sub> [A]*

-   For dependent sums
  - *[Σ<sub>x:A</sub> B] ≔ (Σ<sub>x:⟦A⟧</sub>⟦B⟧, π<sub>Σ</sub><sup>[A],[B]</sup>)*
  - *[(x,y)] ≔ ([x],[y])*
  - *[π<sub>i</sub> t] ≔ π<sub>i</sub> [t]*

-   For dependent products
  - *[Π<sub>x:A</sub> B] ≔ (Π<sub>x:⟦A⟧</sub>⟦B⟧, π<sub>Π</sub><sup>[A],[B]</sup>)*
  - *[λ x:A, M] ≔ λ x:⟦A⟧, [M]*
  - *[t t'] ≔ [t] [t']*

-   For paths
  - *[A = B] ≔ ([A] = [B] ; π<sub>=</sub><sup>[A],[B]</sup>)*
  - *[idpath] ≔ idpath*
  - *[J] ≔ J*

-   For sums
  - *[A + B] ≔ (◯ ([|A|] + [|B|]) ; π<sub>◯</sub><sup>[|A|]+[|B|]</sup>)*
  - *[in<sub>ℓ</sub> t] ≔ η(in<sub>ℓ</sub> [t])*
  - *[in<sub>r</sub> t] ≔ η(in<sub>r</sub> [t])*
  - *[⟨f,g⟩] ≔ ◯<sub>rec</sub><sup>⟦A⟧+⟦B⟧</sup>⟨[f],[g]⟩*

where *π*<sub>*Σ*</sub><sup>*A*, *B*</sup> (resp. *π*<sub>*Π*</sub><sup>*A*, *B*</sup>, resp. *π*<sub>=</sub><sup>*A*, *B*</sup>) is the proof that *Σ*<sub>*x* : *A*</sub>*B* (resp. ∏<sub>*x* : *A*</sub>*B*, resp *A* = *B*) is modal as soon as *A* and *B* are, and π<sub>◯</sub><sup>A</sup> a proof that ◯A is always modal.
