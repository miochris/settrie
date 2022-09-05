
# settrie

Fast subset and superset queries. It implemented Iztok Savnik's proposed data structure [set-trie](https://link.springer.com/chapter/10.1007/978-3-642-40511-2_10).

One difference from Iztok Savnik's data structure is, this implementation doesn't memorize a set which ends in a non-leaf node of existing set.

```rust
use settrie::SetTrie;
fn main(){
    let mut set_trie = SetTrie::new();
    set_trie.insert_set(&[1, 2, 3]);
    set_trie.insert_set(&[1, 2, 3, 5]);
    set_trie.insert_set(&[1, 2, 4]);
    assert_eq!(
        set_trie.get_supersets(&[1, 2]),
        vec![vec![1, 2, 3, 5], vec![1, 2, 4]]
    );
    assert_eq!(set_trie.exist_subset(&vec![1, 2, 3, 5]), true);
    assert_eq!(set_trie.exist_superset(&vec![1, 2]), true);
    assert_eq!(
        set_trie.get_all_supersets(),
        vec![vec![1, 2, 3, 5], vec![1, 2, 4]]
    );
    assert_eq!(set_trie.get_supersets(&[1, 3, 5]), vec![vec![1, 2, 3, 5]]);
    assert_eq!(
        set_trie.get_subsets(&[1, 2, 3, 5, 7]),
        vec![vec![1, 2, 3, 5]]
    );
}

```