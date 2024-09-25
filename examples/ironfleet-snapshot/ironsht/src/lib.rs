#![allow(unused_imports)]
#![allow(unused_attributes)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

mod abstract_end_point_t;
mod abstract_parameters_t;
mod abstract_service_t;
mod app_interface_t;
mod args_t;
mod cmessage_v;
mod delegation_map_t;
mod delegation_map_v;
mod endpoint_hashmap_t;
mod environment_t;
mod hashmap_t;
mod host_impl_t;
mod host_impl_v;
mod host_protocol_t;
mod io_t;
mod keys_t;
mod main_t;
mod marshal_ironsht_specific_v;
mod marshal_v;
mod message_t;
mod net_sht_v;
mod network_t;
mod seq_is_unique_v;
mod single_delivery_model_v;
mod single_delivery_state_v;
mod single_delivery_t;
mod single_message_t;
mod verus_extra; // TODO: maybe move into Verus?

use crate::io_t::EndPoint;
use crate::io_t::NetcReceiveResult;

verus! {

// The function `unflatten_args` takes arguments passed to us by the C# main
// executable and unflattens then into a vector of arguments. C# flattens
// the arguments by contatenating them all together, and passing us an array
// of their lengths.
#[verifier(external)]
#[verus::line_count::ignore]
pub unsafe fn unflatten_args(
    num_args: i32,
    arg_lengths: *const i32,
    _total_arg_length: i32,
    flattened_args: *const u8,
) -> Vec<Vec<u8>> {
    let mut offset: isize = 0;
    let mut args: Vec<Vec<u8>> = Vec::new();
    for i in 0..num_args as isize {
        let arg_length = *arg_lengths.offset(i as isize);
        let arg_array: &[u8] = std::slice::from_raw_parts(
            flattened_args.offset(offset),
            arg_length as usize,
        );
        let arg_vec: std::vec::Vec<u8> = arg_array.to_vec();
        let mut arg: Vec<u8> = Vec::new();
        arg = arg_vec;
        args.push(arg);
        offset += arg_length as isize;
    }
    args
}

#[verifier(external)]
#[verus::line_count::ignore]
pub unsafe fn sht_main_placeholder_to_test_netclient(
    nc: &mut io_t::NetClient,
    args: &Vec<Vec<u8>>,
) {
    for i in 0..args.len() {
        println!("Command-line argument #{}: {:#?}", i+1, args[i]);
    }
    let my_end_point: EndPoint = nc.get_my_end_point();
    println!("My end point: {:#?}", my_end_point.id);
    println!("Current time is {}", nc.get_time());

    let mut message: Vec<u8> = Vec::new();
    message = "Hello, world!".as_bytes().to_vec();
    let _ = nc.send(&my_end_point, &message);

    match nc.receive(0) {
        NetcReceiveResult::Received { sender, message } => {
            println!("Received message {:#?}", message);
        },
        NetcReceiveResult::TimedOut {  } => {
            println!("Timed out");
        },
        NetcReceiveResult::Error {  } => {
            println!("Error");
        },
    }
    std::thread::sleep(std::time::Duration::from_millis(1000));

    match nc.receive(0) {
        NetcReceiveResult::Received { sender, message } => {
            println!("Received message {:#?}", message);
        },
        NetcReceiveResult::TimedOut {  } => {
            println!("Timed out");
        },
        NetcReceiveResult::Error {  } => {
            println!("Error");
        },
    }
}

// This routine is exported to the C# main executable containing the I/O
// framework. This lets the I/O framework allocate Rust buffers that it can fill
// and return to us.
//
// For instance, suppose the I/O framework is about to receive a packet, and has
// learned that packet's length. It will call `allocate_buffer`, and we'll
// return to it two things: `buffer_ptr`, a pointer to a region of memory with
// length `length`, and `box_vec_ptr`, a pointer that it will return to us when
// we ask to receive a message.
#[verifier(external)]
#[no_mangle]
#[verus::line_count::ignore]
pub unsafe extern "C" fn allocate_buffer(
    length: u64,
    box_vec_ptr: *mut *mut std::vec::Vec<u8>,
    buffer_ptr: *mut *mut u8,
) {
    // Allocate a std::vec::Vec<u8> with the given length.
    let mut v: std::vec::Vec<u8> = std::vec::Vec::<u8>::with_capacity(length as usize);
    v.set_len(length as usize);

    // Box the vector.
    let mut b: Box<std::vec::Vec<u8>> = Box::<std::vec::Vec<u8>>::new(v);

    // Return the raw pointer to the vector's buffer as `*buffer_ptr`.
    *buffer_ptr = (*b).as_mut_ptr();

    // Return the raw pointer to the Box as `*box_vec_ptr`.
    *box_vec_ptr = Box::<std::vec::Vec<u8>>::into_raw(b);
}

// This routine is exported to the C# main executable containing the I/O
// framework. This lets the I/O framework deallocate a Rust buffers that
// it allocated with `allocate_buffer` that it was planning to return to
// us but has now decided it doesn't want to return to us. For instance,
// if the I/O framework allocated it to store an incoming packet, but
// detected that the connection closed, it needs to free the buffer.
#[verifier(external)]
#[verus::line_count::ignore]
#[no_mangle]
pub unsafe extern "C" fn free_buffer(box_vec_ptr: *mut std::vec::Vec<u8>) {
    // Convert back from a raw pointer to a Box so that when the Box
    // goes out of scope at the end of this function, it will be
    // freed.
    let _box_vec: Box<std::vec::Vec<u8>> = Box::<std::vec::Vec<u8>>::from_raw(box_vec_ptr);
}

#[verifier(external)]
#[verus::line_count::ignore]
#[no_mangle]
pub unsafe extern "C" fn sht_main_wrapper(
    num_args: i32,
    arg_lengths: *const i32,
    total_arg_length: i32,
    flattened_args: *const u8,
    get_my_end_point_func: extern "C" fn (*mut *mut std::vec::Vec<u8>),
    get_time_func: extern "C" fn () -> u64,
    receive_func: extern "C" fn (
        i32,
        *mut bool,
        *mut bool,
        *mut *mut std::vec::Vec<u8>,
        *mut *mut std::vec::Vec<u8>,
    ),
    send_func: extern "C" fn (u64, *const u8, u64, *const u8) -> bool,
) -> i32 {
    let args: Vec<Vec<u8>> = unflatten_args(
        num_args,
        arg_lengths,
        total_arg_length,
        flattened_args,
    );

    let mut my_end_point_vec_ptr = std::mem::MaybeUninit::<*mut std::vec::Vec<u8>>::uninit();
    get_my_end_point_func(my_end_point_vec_ptr.as_mut_ptr());
    let my_end_point_ptr: *mut std::vec::Vec<u8> = my_end_point_vec_ptr.assume_init();
    let my_end_point_box: Box<std::vec::Vec<u8>> = Box::<std::vec::Vec<u8>>::from_raw(
        my_end_point_ptr,
    );
    let my_end_point_vec: std::vec::Vec<u8> = *my_end_point_box;
    let mut my_end_point: Vec<u8> = Vec::new();
    my_end_point = my_end_point_vec;

    let mut nc = crate::io_t::NetClient::new(
        EndPoint { id: my_end_point },
        get_time_func,
        receive_func,
        send_func,
    );
    match main_t::sht_main(nc, args) {
        Ok(_) => 0,
        Err(_) => 1,
    }
}

} // verus!
