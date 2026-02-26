# SwiftSync Hintsfile

_SwiftSync_ is a protocol to accelerate the initial block download for Bitcoin clients. The protocol requires hints as to what coins will remain unspent at a particular block height throughout the chain history. This crate is an implementation of a file that encodes such hints. In essence, it is an concise encoding of the UTXO set.

## Methodology

The file encodes monotonically increasing indices within a block for which coins remain unspent. Given a block of `M` elements, suppose `N` are not spent, then the file encodes these positions with $`2n + n \lceil \log_2(m/n) \rceil`$ bits. This is near the optimum of $`\log_2 \binom{m}{n}`$

The technique used for this encoding was developed by _Elias_ and _Fano_, which you may read about [here](https://t.holmium.no/dia/elias-fano/).

## Usage

```cargo add hintsfile```

```rust
use hintsfile::Hintsfile;

// Load a file
let hints = Hintsfile::from_reader(&mut file)?;
```
