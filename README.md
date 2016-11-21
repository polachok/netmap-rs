# netmap-rs
Higher level interface to netmap

This is a work in progress. And it's totally unsafe.

Be sure to turn all NIC offloads off before testing - netmap doesn't use NIC
offloads.

Usage example
=============
```rust
extern crate libc;
extern crate netmap;

use std::env;
use netmap::*;

fn move_packets(src: &mut netmap::NetmapDescriptor, dst: &mut netmap::NetmapDescriptor) {
    {
        let mut rx_slots = src.rx_iter().flat_map(|rx_ring| rx_ring.iter());
        'rings: for tx_ring in dst.tx_iter() {
            let mut tx_slot_iter = tx_ring.iter_mut();
            'slots: loop {
                match tx_slot_iter.next() {
                    None => break 'slots,
                    Some(tx_slot_buf) => {
                        match rx_slots.next() {
                            None => {
                                // "End of RX queue.
                                tx_slot_iter.give_back();
                                break 'rings;
                            }
                            Some(rx_slot_buf) => {
                                let tgt_buf =
                                    &mut tx_slot_buf.1[0..rx_slot_buf.0.get_len() as usize];
                                tgt_buf.copy_from_slice(rx_slot_buf.1);
                                tx_slot_buf.0.set_len(rx_slot_buf.0.get_len());
                            }
                        }
                    }
                }
            }
        }
    };
    // Tell the kernel it can use the slots we've consumed.
    for ring in src.rx_iter() {
        ring.head_from_cur();
    }
    // Tell the kernel it can send the slots we've populated.
    for ring in dst.tx_iter() {
        ring.head_from_cur();
    }
}

fn main() {
    let iface = env::args().nth(1).expect("expected interface name as argument (e.g. eth0)");
    let mut nm_wire = NetmapDescriptor::new(&iface).expect("can't open netmap for interface");
    let mut nm_host = NetmapDescriptor::new(&(iface + "^")).expect("can't open netmap host interface");
    let mut pollfds: Vec<libc::pollfd> = Vec::with_capacity(2);
    pollfds.push(libc::pollfd{ nm_wire.get_fd(), events: 0, revents: 0 });
    pollfds.push(libc::pollfd{ nm_host.get_fd(), events: 0, revents: 0 });
    loop {
      	for pollfd in pollfdss.iter_mut() {
	    pollfd.events = libc::POLLIN;
	    pollfd.revents = 0;
	}
	if let Some(first) = pollfds.first_mut() {
	    match unsafe {libc::poll(first as *mut libc::pollfd, 2, 1000)} {
	      x if x < 0 => panic!("poll failure"),
	      x if x == 0 => continue,
	      _ => ()
	    }
	} else {
	  panic!("no fd vec?")
	}
        // A netmap poll error can mean the rings get reset: loop again.
        for pollfd in pollfds.iter() {
            if pollfd.revents & libc::POLLERR == libc::POLLERR {
                continue;
            }
        }
	move_packets(&mut nm_host, &mut nm_wire);
	move_packets(&mut nm_wire, &mut nm_host);
    }
}
```
