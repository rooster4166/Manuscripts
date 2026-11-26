import GallaiLean.LeafDictionary

/-!
# Elementary moves for Fan's addible-edge lemma

* `PathDecomp.replace`: replace one path by a path of a new graph whose edge set differs only
  on that path. The other paths are transferred unchanged.
* `PathDecomp.append_move`: a path with an end at `t` that avoids `u` absorbs the new edge `tu`.
  The end moves

end Gallai
