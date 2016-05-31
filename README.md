# netmap-rs
Higher level interface to netmap

This is a work in progress. And it's totally unsafe.

Usage example
=============
```rust
extern crate netmap;

use std::env;
use netmap::*;

fn main() {
    let iface = env::args().nth(1).expect("expected interface name as argument (e.g. eth0)");
    let mut nm = NetmapDescriptor::new(&iface).expect("can't open netmap for interface");
    loop {
        nm.poll(Direction::Input);
        for ring in nm.rx_iter() {
            for (_, buf) in ring.iter() {
                println!("received {:?}", buf);
            }
        }
    }
}
```
