/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include "util/lp/numeric_pair.h"
#include "util/lp/binary_heap_priority_queue.cpp"
namespace lean {
template binary_heap_priority_queue<int>::binary_heap_priority_queue(unsigned int);
template unsigned binary_heap_priority_queue<int>::dequeue();
template void binary_heap_priority_queue<int>::enqueue(unsigned int, int const&);
template void binary_heap_priority_queue<int>::remove(unsigned int);
template unsigned binary_heap_priority_queue<numeric_pair<mpq> >::dequeue();
template void binary_heap_priority_queue<numeric_pair<mpq> >::enqueue(unsigned int, numeric_pair<mpq> const&);
template void binary_heap_priority_queue<numeric_pair<mpq> >::resize(unsigned int);
template binary_heap_priority_queue<unsigned int>::binary_heap_priority_queue(unsigned int);
template unsigned binary_heap_priority_queue<unsigned int>::dequeue();
template void binary_heap_priority_queue<unsigned int>::enqueue(unsigned int, unsigned int const&);
template void binary_heap_priority_queue<unsigned int>::remove(unsigned int);
}
