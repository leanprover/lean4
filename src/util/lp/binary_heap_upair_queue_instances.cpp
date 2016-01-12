/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE

  Author: Lev Nachmanson
*/
#include "util/lp/binary_heap_upair_queue.cpp"
namespace lean {
template binary_heap_upair_queue<int>::binary_heap_upair_queue(unsigned int);
template binary_heap_upair_queue<unsigned int>::binary_heap_upair_queue(unsigned int);
template unsigned binary_heap_upair_queue<int>::dequeue_available_spot();
template unsigned binary_heap_upair_queue<unsigned int>::dequeue_available_spot();
template void binary_heap_upair_queue<int>::enqueue(unsigned int, unsigned int, int const&);
template void binary_heap_upair_queue<int>::remove(unsigned int, unsigned int);
template void binary_heap_upair_queue<unsigned int>::remove(unsigned int, unsigned int);
template void binary_heap_upair_queue<int>::dequeue(unsigned int&, unsigned int&);
template void binary_heap_upair_queue<unsigned int>::enqueue(unsigned int, unsigned int, unsigned int const&);
template void binary_heap_upair_queue<unsigned int>::dequeue(unsigned int&, unsigned int&);
}
