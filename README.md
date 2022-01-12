# roulette-tree

A red-black tree.  For didactic purposes.

## VecTree

A red-black tree implemented by holding nodes in a `Vec`.

Pointers are implemented as `Option<usize>`; `usize` is just an index into the inner `Vec`.

### Implementation Notes

While canonical implementations of binary trees allocate array space for all 2^d possible nodes (where d is the depth of the tree), so that the children of a node living at index `i`
can find its children at `2i + 1` and `2i + 2` respectively, this representation instead uses the array as a memory arena, with indices as pointers of sorts.
This means the tree is tightly packed in memory, and shares the same memory semantics as a `Vec`.

This also means that nodes which are removed from the tree are essentially leaked.  They are replaced with a `None`, or a "null pointer".  
However, since `Vec` and most other vector implementations do not lose storage capacity when elements are removed, this is not an issue as long as we insert new nodes into these emptied spots in the `Vec` - which we do.

Only when the tree is emptied does it fully deallocate the inner Vec.

Why use a Vec over pointers and heap allocation?  Well, pointers (dynamic object creation) are less performant and the fragmented heap allocation you get with pointers to nowhere struggles to exploit the cache.  We might lose the ability to deallocate individual elements, but we gain the ability of a fast linear search (which excels for small trees with little deletions), instant indexing of the tree, reuse of the `Vec` API if we need etc.

The most important motivation, however, is the fact that Rust does not appreciate circular reference - and so if we used pointers, we would never be able to refer to parents.  Rust's disdain of circular reference holds similarity to functional immutable data structures, where you can typically only traverse one way.  This way of programming encourages memory safety at the cost of ease of use - of course, it's not like using a `Vec` is hard.

### Does Rust use a RB Tree?

No; newer languages tend to use B-Trees.  Java and C++ use red-black trees in their implementations of set and map, but Rust uses a B-Tree.
Read https://doc.rust-lang.org/std/collections/struct.BTreeMap.html for more information.  

A B-tree is considerably different in representation than a red-black tree, with a red-black tree being a genuine binary search tree (albeit balanced), and the B-tree being superior in many ways.  Nonetheless, one can demonstrate that red-black trees are a subset of B-trees by moving red nodes up to join their parents in a 2/3-node.

For more information about B-trees and Rust's implementation of them in the standard library, see Alexis' own blog: https://cglab.ca/~abeinges/blah/rust-btree-case/
