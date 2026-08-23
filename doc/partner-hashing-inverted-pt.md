# Partner Hashing for Inverted Page Tables: Adapting Bender-Kuszmaul-Zhou to Superpages

## The BKZ Paper in Brief

Bender, Kuszmaul, and Zhou (arXiv:2503.13628) achieve a remarkable result: **an open-addressed hash table that operates at load factor 1 with O(1) worst-case queries and O(1) high-probability insertions/deletions**, using only O(1)-wise independent hash functions.

The key technique is **partner hashing**: encoding metadata in the *relative ordering* of elements. An array of n elements stores Θ(n log n) bits of information in the permutation itself. Two "partner" keys swap positions to encode a RAM word. The retrieval structure (mapping keys to their logical offsets) is itself stored in the encoded RAM, without cyclic dependency.

Key properties:
- **Load factor 1**: No empty slots. The array is a permutation of its keys.
- **Dynamic resizing**: As n changes, the hash table grows/shrinks by 1 slot per operation.
- **Constant-time ops**: Queries O(1) worst-case; inserts/deletes O(1) whp.
- **O(1)-wise independent hash**: Only needs simple hash functions, not fully random.

## The Inverted Page Table Problem

An inverted page table maps virtual addresses to physical addresses using a hash of the VA:

```
hash(VA) → slot in table
Table[slot] = {PA, permissions, size, valid}
```

**Current challenges**:
1. **Superpage handling**: How to store entries of different sizes (4KB, 64KB, 1MB, etc.) in one hash table
2. **Load factor**: Traditional hash tables need 50-75% load factor; inverted tables waste physical RAM
3. **Collision resolution**: Open addressing degrades; chaining needs pointers
4. **Concurrent access**: TLB lookups must be fast; concurrent updates need locking

## Adapting Partner Hashing to Inverted Page Tables

### Why BKZ Translates Well

The inverted page table is *exactly* an open-addressed hash table:
- **Keys**: Virtual page numbers (VPN)
- **Values**: Physical page numbers (PFN) + permissions + size
- **Hash function**: hash(VPN) → slot index
- **Load factor**: Traditionally ≤ 75%; BKZ enables 100%

Partner hashing solves the key problems:

#### 1. Metadata Storage Without Extra Space

In an inverted page table, each entry needs:
- VA tag (for collision detection): ~48 bits (for 48-bit VA)
- PA: ~56 bits (for 56-bit physical address)
- Permissions: 9 bits (R, W, X, U, G, A, D, V, plus reserved)
- Size encoding: 6 bits (for 56 sizes)
- **Total**: ~119 bits

With partner hashing, the metadata (size encoding, permissions, valid bits) can be encoded in the *ordering* of entries. The PA is the "key" stored explicitly, and everything else is implicit in the permutation.

#### 2. Load Factor 1

Partner hashing operates at load factor 1. For an inverted page table:
- **Before**: 1 entry per 2 physical pages → table size = 50% of physical RAM
- **After**: 1 entry per 1 physical page → table size = 100% of physical RAM (but no waste!)

Wait — this seems counterintuitive. Let me reconsider.

Actually, the inverted table maps VPN → PFN. The number of *mappings* is at most the number of physical pages (since each PFN maps to at most one VPN). So:
- **Number of entries**: ≤ physical pages
- **Table size**: 1 entry per physical page (load factor 1)
- **Space**: n entries × 128 bits = 128n bits

For 64GB RAM with 4KB pages: 2^30 entries × 128 bits = 2^37 bytes = 128GB. **This is larger than RAM itself!**

This is the fundamental problem: **inverted page tables are space-prohibitive for small page sizes**. The table is sized to physical RAM, not to the number of mappings.

#### 3. The Superpage Opportunity

**This is where partner hashing becomes transformative for inverted tables:**

With W=1, K=256B, a 64KB superpage mapping occupies ONE entry (not 256 entries). The number of entries needed is:
```
entries = total_RAM / average_superpage_size
```

If the average superpage size is 64KB:
- entries = 64GB / 64KB = 2^20
- Table size = 2^20 × 128 bits = 16MB

**This is 8000× smaller than the 4KB case!**

### The Design: Partner-Hashed Inverted Page Table (PHIPT)

#### Entry Format (128 bits)

```
[127:64]  VA_tag[47:0] (48 bits) + size[53:48] (6 bits) + reserved[63:54] (10 bits)
[63:0]    PA[55:0] (56 bits) + perms[64:56] (9 bits) + valid[65] (1 bit) + reserved[127:66] (62 bits)
```

But wait — partner hashing encodes metadata in the *ordering*. So the entry itself can be simpler:

```
[127:64]  VA_tag[47:0] (48 bits) + reserved[127:48] (16 bits)
[63:0]    PA[55:0] (56 bits) + reserved[63:56] (8 bits)
```

The size, permissions, and valid bits are encoded in the *partner pairing* (which partner bin the entry is paired with).

#### Hash Function Design

The hash function must be **superpage-aware**:

```python
def hash_vpn(vpn, size_log2):
    """
    Hash a virtual page number for a given superpage size.
    
    For a superpage of size 2^size_log2:
    - VPN bits [size_log2-1:0] are the page offset (ignored for hashing)
    - VPN bits [47:size_log2] are the virtual superpage number
    - Hash this superpage number to get the slot
    """
    superpage_vpn = vpn >> size_log2
    return hash(superpage_vpn) % table_size
```

**Critical property**: All VAs within a superpage hash to the same slot. This is ensured by ignoring the lower bits.

#### Partner Pairing for Metadata

In BKZ, two keys swap positions to encode a RAM word. In PHIPT:

- **Index bins**: Store the PA (the "key")
- **Partner bins**: Encode metadata (size, permissions) in which partner bin the entry is paired with

For a mapping with size=64KB and perms=0b110 (RW):
- The entry in the index bin is paired with an entry in partner bin (size XOR perms XOR random_bits)
- Reading the partner bin index reveals the metadata

#### Dynamic Resizing

Partner hashing supports dynamic resizing (Section 5 of BKZ). For an inverted page table:
- When a new mapping is added, the table grows by 1 slot
- When a mapping is removed, the table shrinks by 1 slot
- **No periodic rehashing needed!**

This is a huge advantage over traditional hash tables that need occasional rehashing.

## Handling Many Superpage Sizes

### The 56-Size Spectrum

With W=1, K=256B, the possible superpage sizes are:
```
256B, 512B, 1KB, 2KB, 4KB, 8KB, 16KB, 32KB, 64KB, 128KB, 256KB,
512KB, 1MB, 2MB, 4MB, 8MB, 16MB, 32MB, 64MB, 128MB, 256MB, 512MB,
1GB, 2GB, 4GB, 8GB, 16GB, 32GB, 64GB
```

That's 29 sizes (powers of 2). With additional non-power-of-2 sizes (e.g., 6×256B=1.5KB), we could reach 56.

### The Problem: Size Encoding

With 56 sizes, we need ⌈log₂(56)⌉ = 6 bits for size encoding. This fits easily in the 128-bit entry.

### The Problem: Hash Consistency

For each size, the hash function must be consistent:
- All VAs within a 64KB superpage hash to the same slot
- All VAs within a 1MB superpage hash to the same slot
- But a 64KB superpage and a 1MB superpage covering the same VA range must hash to *different* slots (different mappings!)

**Solution**: Hash on the superpage number, not just the VPN:
```python
def hash_vpn(vpn, size_log2):
    superpage_vpn = vpn >> size_log2
    # Include size in the hash to distinguish different sizes
    return hash(superpage_vpn, size_log2) % table_size
```

### The Problem: Overlapping Superpages

A VA might be covered by multiple superpages:
- A 64KB superpage covering [0x10000, 0x20000)
- A 1MB superpage covering [0x00000, 0x100000)

The TLB must find the *most specific* (smallest) superpage that covers the VA.

**Solution**: Use a separate TLB with size-aware matching (already implemented in Tessera). The inverted table stores all mappings; the TLB caches the relevant ones.

## Radical Idea: Eliminate the Hash Table Entirely

### Pure Partner-Ordered Storage

Instead of hashing, use the *permutation itself* as the translation function:

```python
def translate(vpn):
    # The table is a permutation of all possible VPNs
    # vpn is at position vpn in the permutation
    # Read the PA at that position
    return table[vpn]
```

This is O(1) with no hashing, no collisions, no probing!

**Problem**: The table has 2^48 entries (for 48-bit VA). That's 256 petabytes × 128 bits = 4 exabytes. Way too large.

### Segmented Partner Hashing

Use an SLB-like structure to cache hot segments:
- **SLB**: 256 entries, each covering a 256MB segment (like POWER)
- **PHIPT**: Small hash table for the SLB miss path
- **Partner hashing**: Encodes metadata in the SLB entries themselves

This combines the best of both worlds:
- SLB gives O(1) for hot segments
- PHIPT handles cold translations efficiently
- Partner hashing eliminates extra metadata storage

## Comparison with Traditional Approaches

| Approach | Load Factor | Query Time | Insert/Delete | Metadata Space |
|----------|-------------|------------|---------------|----------------|
| Linear probing | ≤ 75% | O(1/ε) | O(1/ε) | 0 (in entry) |
| Cuckoo hashing | ≤ 50% | O(1) | O(1) | 0 (in entry) |
| Partner hashing (BKZ) | 100% | O(1) | O(1) | 0 (in permutation) |
| **PHIPT (proposed)** | 100% | O(1) | O(1) | 0 (in permutation) |

## Open Questions

1. **Concurrent access**: Partner hashing needs atomic swaps for updates. How to make this lock-free for TLB lookups?

2. **TLB interaction**: The TLB caches entries from the PHIPT. How to invalidate TLB entries when PHIPT entries move (due to partner swapping)?

3. **Hash function quality**: BKZ uses O(1)-wise independent hash functions. Are these sufficient for address translation, or do we need better distribution?

4. **Superpage promotion/demotion**: When a 64KB superpage is split into 16×4KB pages, how to update the PHIPT efficiently?

5. **NUMA considerations**: Should the PHIPT be per-NUMA-node or global? Partner hashing works either way, but locality matters.

## References

- Bender, M.A., Kuszmaul, W., Zhou, R. (2025). "Optimal Non-Oblivious Open Addressing." arXiv:2503.13628.
- IBM Power ISA (2023). Hash Page Table specification.
- Sun UltraSPARC Architecture Manual (2006). TSB specification.
- Tessera mmu-variants.md. Software-refill vs hardware-walker analysis.

---

*This document explores the adaptation of partner hashing to inverted page tables for the Tessera verification project. The key insight is that partner hashing enables load-factor-1 operation with O(1) operations, which is transformative for inverted page tables where space is the primary bottleneck.*
