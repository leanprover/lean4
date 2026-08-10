// Lean compiler output
// Module: Std.Net.Addr
// Imports: public import Init.System.IO public import Init.Data.Vector.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instDecidableEqUInt8___boxed(lean_object*, lean_object*);
uint8_t l_Array_instDecidableEqImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqUInt16___boxed(lean_object*, lean_object*);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedMACAddr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedMACAddr_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedMACAddr_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedMACAddr;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqMACAddr_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqMACAddr_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqMACAddr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqMACAddr___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedIPv4Addr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedIPv4Addr_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPv4Addr_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPv4Addr;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv4Addr_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv4Addr_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv4Addr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv4Addr___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedSocketAddressV4_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddressV4_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddressV4;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV4_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV4_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedIPv6Addr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedIPv6Addr_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPv6Addr_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPv6Addr;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv6Addr_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv6Addr_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv6Addr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv6Addr___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedSocketAddressV6_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedSocketAddressV6_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddressV6_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddressV6;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV6_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV6_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedIPAddr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedIPAddr_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPAddr_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPAddr;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPAddr_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPAddr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedSocketAddress_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedSocketAddress_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddress_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddress;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddress_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddress(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instInhabitedAddressFamily_default;
LEAN_EXPORT uint8_t l_Std_Net_instInhabitedAddressFamily;
LEAN_EXPORT uint8_t l_Std_Net_AddressFamily_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqAddressFamily(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqAddressFamily___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofParts(uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofParts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_pton_v4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofString___boxed(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_toString___boxed(lean_object*);
static const lean_closure_object l_Std_Net_IPv4Addr_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_IPv4Addr_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_IPv4Addr_instToString___closed__0 = (const lean_object*)&l_Std_Net_IPv4Addr_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_IPv4Addr_instToString = (const lean_object*)&l_Std_Net_IPv4Addr_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_instCoeIPAddr___lam__0(lean_object*);
static const lean_closure_object l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_IPv4Addr_instCoeIPAddr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0 = (const lean_object*)&l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_IPv4Addr_instCoeIPAddr = (const lean_object*)&l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0_value;
static const lean_string_object l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0 = (const lean_object*)&l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Net_SocketAddressV4_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_SocketAddressV4_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_SocketAddressV4_instToString___closed__0 = (const lean_object*)&l_Std_Net_SocketAddressV4_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_SocketAddressV4_instToString = (const lean_object*)&l_Std_Net_SocketAddressV4_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instCoeSocketAddress___lam__0(lean_object*);
static const lean_closure_object l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_SocketAddressV4_instCoeSocketAddress___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0 = (const lean_object*)&l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_SocketAddressV4_instCoeSocketAddress = (const lean_object*)&l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofParts(uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofParts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_pton_v6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofString___boxed(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_toString___boxed(lean_object*);
static const lean_closure_object l_Std_Net_IPv6Addr_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_IPv6Addr_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_IPv6Addr_instToString___closed__0 = (const lean_object*)&l_Std_Net_IPv6Addr_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_IPv6Addr_instToString = (const lean_object*)&l_Std_Net_IPv6Addr_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_instCoeIPAddr___lam__0(lean_object*);
static const lean_closure_object l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_IPv6Addr_instCoeIPAddr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0 = (const lean_object*)&l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_IPv6Addr_instCoeIPAddr = (const lean_object*)&l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0_value;
static const lean_string_object l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0 = (const lean_object*)&l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0_value;
static const lean_string_object l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]:"};
static const lean_object* l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1 = (const lean_object*)&l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Net_SocketAddressV6_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_SocketAddressV6_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_SocketAddressV6_instToString___closed__0 = (const lean_object*)&l_Std_Net_SocketAddressV6_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_SocketAddressV6_instToString = (const lean_object*)&l_Std_Net_SocketAddressV6_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instCoeSocketAddress___lam__0(lean_object*);
static const lean_closure_object l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_SocketAddressV6_instCoeSocketAddress___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0 = (const lean_object*)&l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_SocketAddressV6_instCoeSocketAddress = (const lean_object*)&l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Net_IPAddr_family(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_family___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_toString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_toString___boxed(lean_object*);
static const lean_closure_object l_Std_Net_IPAddr_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_IPAddr_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_IPAddr_instToString___closed__0 = (const lean_object*)&l_Std_Net_IPAddr_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_IPAddr_instToString = (const lean_object*)&l_Std_Net_IPAddr_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Net_SocketAddress_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_SocketAddress_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_SocketAddress_instToString___closed__0 = (const lean_object*)&l_Std_Net_SocketAddress_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_SocketAddress_instToString = (const lean_object*)&l_Std_Net_SocketAddress_instToString___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Net_SocketAddress_family(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_family___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ipAddr(lean_object*);
LEAN_EXPORT uint16_t l_Std_Net_SocketAddress_port(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_port___boxed(lean_object*);
static const lean_string_object l_Std_Net_instInhabitedInterfaceAddress_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Net_instInhabitedInterfaceAddress_default___closed__0 = (const lean_object*)&l_Std_Net_instInhabitedInterfaceAddress_default___closed__0_value;
static lean_once_cell_t l_Std_Net_instInhabitedInterfaceAddress_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedInterfaceAddress_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedInterfaceAddress_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedInterfaceAddress;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqInterfaceAddress_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqInterfaceAddress(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress___boxed(lean_object*, lean_object*);
lean_object* lean_uv_interface_addresses();
LEAN_EXPORT lean_object* l_Std_Net_interfaceAddresses___boxed(lean_object*);
static lean_object* _init_l_Std_Net_instInhabitedMACAddr_default___closed__0(void){
_start:
{
uint8_t v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_1_ = 0;
v___x_2_ = lean_unsigned_to_nat(6u);
v___x_3_ = lean_box(v___x_1_);
v___x_4_ = lean_mk_array(v___x_2_, v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedMACAddr_default(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Std_Net_instInhabitedMACAddr_default___closed__0, &l_Std_Net_instInhabitedMACAddr_default___closed__0_once, _init_l_Std_Net_instInhabitedMACAddr_default___closed__0);
return v___x_5_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedMACAddr(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Std_Net_instInhabitedMACAddr_default;
return v___x_6_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqMACAddr_decEq(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_alloc_closure((void*)(l_instDecidableEqUInt8___boxed), 2, 0);
v___x_10_ = l_Array_instDecidableEqImpl___redArg(v___x_9_, v_x_7_, v_x_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqMACAddr_decEq___boxed(lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_x_11_, v_x_12_);
lean_dec_ref(v_x_12_);
lean_dec_ref(v_x_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqMACAddr(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_x_15_, v_x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqMACAddr___boxed(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_Std_Net_instDecidableEqMACAddr(v_x_18_, v_x_19_);
lean_dec_ref(v_x_19_);
lean_dec_ref(v_x_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv4Addr_default___closed__0(void){
_start:
{
uint8_t v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_22_ = 0;
v___x_23_ = lean_unsigned_to_nat(4u);
v___x_24_ = lean_box(v___x_22_);
v___x_25_ = lean_mk_array(v___x_23_, v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv4Addr_default(void){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_obj_once(&l_Std_Net_instInhabitedIPv4Addr_default___closed__0, &l_Std_Net_instInhabitedIPv4Addr_default___closed__0_once, _init_l_Std_Net_instInhabitedIPv4Addr_default___closed__0);
return v___x_26_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv4Addr(void){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Std_Net_instInhabitedIPv4Addr_default;
return v___x_27_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv4Addr_decEq(lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_alloc_closure((void*)(l_instDecidableEqUInt8___boxed), 2, 0);
v___x_31_ = l_Array_instDecidableEqImpl___redArg(v___x_30_, v_x_28_, v_x_29_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv4Addr_decEq___boxed(lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_x_32_, v_x_33_);
lean_dec_ref(v_x_33_);
lean_dec_ref(v_x_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv4Addr(lean_object* v_x_36_, lean_object* v_x_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_x_36_, v_x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv4Addr___boxed(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_Net_instDecidableEqIPv4Addr(v_x_39_, v_x_40_);
lean_dec_ref(v_x_40_);
lean_dec_ref(v_x_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0(void){
_start:
{
uint16_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = 0;
v___x_44_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_45_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set_uint16(v___x_45_, sizeof(void*)*1, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV4_default(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Std_Net_instInhabitedSocketAddressV4_default___closed__0, &l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0);
return v___x_46_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV4(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Net_instInhabitedSocketAddressV4_default;
return v___x_47_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV4_decEq(lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_addr_50_; uint16_t v_port_51_; lean_object* v_addr_52_; uint16_t v_port_53_; uint8_t v___x_54_; 
v_addr_50_ = lean_ctor_get(v_x_48_, 0);
v_port_51_ = lean_ctor_get_uint16(v_x_48_, sizeof(void*)*1);
v_addr_52_ = lean_ctor_get(v_x_49_, 0);
v_port_53_ = lean_ctor_get_uint16(v_x_49_, sizeof(void*)*1);
v___x_54_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_addr_50_, v_addr_52_);
if (v___x_54_ == 0)
{
return v___x_54_;
}
else
{
uint8_t v___x_55_; 
v___x_55_ = lean_uint16_dec_eq(v_port_51_, v_port_53_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV4_decEq___boxed(lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_x_56_, v_x_57_);
lean_dec_ref(v_x_57_);
lean_dec_ref(v_x_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV4(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_x_60_, v_x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV4___boxed(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Std_Net_instDecidableEqSocketAddressV4(v_x_63_, v_x_64_);
lean_dec_ref(v_x_64_);
lean_dec_ref(v_x_63_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv6Addr_default___closed__0(void){
_start:
{
uint16_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_67_ = 0;
v___x_68_ = lean_unsigned_to_nat(8u);
v___x_69_ = lean_box(v___x_67_);
v___x_70_ = lean_mk_array(v___x_68_, v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv6Addr_default(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_obj_once(&l_Std_Net_instInhabitedIPv6Addr_default___closed__0, &l_Std_Net_instInhabitedIPv6Addr_default___closed__0_once, _init_l_Std_Net_instInhabitedIPv6Addr_default___closed__0);
return v___x_71_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv6Addr(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Std_Net_instInhabitedIPv6Addr_default;
return v___x_72_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv6Addr_decEq(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_alloc_closure((void*)(l_instDecidableEqUInt16___boxed), 2, 0);
v___x_76_ = l_Array_instDecidableEqImpl___redArg(v___x_75_, v_x_73_, v_x_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv6Addr_decEq___boxed(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_x_77_, v_x_78_);
lean_dec_ref(v_x_78_);
lean_dec_ref(v_x_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv6Addr(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_x_81_, v_x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv6Addr___boxed(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_Net_instDecidableEqIPv6Addr(v_x_84_, v_x_85_);
lean_dec_ref(v_x_85_);
lean_dec_ref(v_x_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV6_default___closed__0(void){
_start:
{
uint16_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = 0;
v___x_89_ = l_Std_Net_instInhabitedIPv6Addr_default;
v___x_90_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set_uint16(v___x_90_, sizeof(void*)*1, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV6_default(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Std_Net_instInhabitedSocketAddressV6_default___closed__0, &l_Std_Net_instInhabitedSocketAddressV6_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddressV6_default___closed__0);
return v___x_91_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV6(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_Net_instInhabitedSocketAddressV6_default;
return v___x_92_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV6_decEq(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_addr_95_; uint16_t v_port_96_; lean_object* v_addr_97_; uint16_t v_port_98_; uint8_t v___x_99_; 
v_addr_95_ = lean_ctor_get(v_x_93_, 0);
v_port_96_ = lean_ctor_get_uint16(v_x_93_, sizeof(void*)*1);
v_addr_97_ = lean_ctor_get(v_x_94_, 0);
v_port_98_ = lean_ctor_get_uint16(v_x_94_, sizeof(void*)*1);
v___x_99_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_addr_95_, v_addr_97_);
if (v___x_99_ == 0)
{
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = lean_uint16_dec_eq(v_port_96_, v_port_98_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV6_decEq___boxed(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_x_101_, v_x_102_);
lean_dec_ref(v_x_102_);
lean_dec_ref(v_x_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV6(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_x_105_, v_x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV6___boxed(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Std_Net_instDecidableEqSocketAddressV6(v_x_108_, v_x_109_);
lean_dec_ref(v_x_109_);
lean_dec_ref(v_x_108_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx(lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_unsigned_to_nat(0u);
return v___x_113_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_unsigned_to_nat(1u);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx___boxed(lean_object* v_x_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Net_IPAddr_ctorIdx(v_x_115_);
lean_dec_ref(v_x_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___redArg(lean_object* v_t_117_, lean_object* v_k_118_){
_start:
{
lean_object* v_addr_119_; lean_object* v___x_120_; 
v_addr_119_ = lean_ctor_get(v_t_117_, 0);
lean_inc_ref(v_addr_119_);
lean_dec_ref(v_t_117_);
v___x_120_ = lean_apply_1(v_k_118_, v_addr_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim(lean_object* v_motive_121_, lean_object* v_ctorIdx_122_, lean_object* v_t_123_, lean_object* v_h_124_, lean_object* v_k_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_123_, v_k_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___boxed(lean_object* v_motive_127_, lean_object* v_ctorIdx_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_k_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_Net_IPAddr_ctorElim(v_motive_127_, v_ctorIdx_128_, v_t_129_, v_h_130_, v_k_131_);
lean_dec(v_ctorIdx_128_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim___redArg(lean_object* v_t_133_, lean_object* v_v4_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_133_, v_v4_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim(lean_object* v_motive_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_v4_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_137_, v_v4_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim___redArg(lean_object* v_t_141_, lean_object* v_v6_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_141_, v_v6_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim(lean_object* v_motive_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_v6_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_145_, v_v6_147_);
return v___x_148_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr_default___closed__0(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr_default(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Std_Net_instInhabitedIPAddr_default___closed__0, &l_Std_Net_instInhabitedIPAddr_default___closed__0_once, _init_l_Std_Net_instInhabitedIPAddr_default___closed__0);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_Net_instInhabitedIPAddr_default;
return v___x_152_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPAddr_decEq(lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_153_) == 0)
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v_addr_155_; lean_object* v_addr_156_; uint8_t v___x_157_; 
v_addr_155_ = lean_ctor_get(v_x_153_, 0);
v_addr_156_ = lean_ctor_get(v_x_154_, 0);
v___x_157_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_addr_155_, v_addr_156_);
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
}
else
{
if (lean_obj_tag(v_x_154_) == 0)
{
uint8_t v___x_159_; 
v___x_159_ = 0;
return v___x_159_;
}
else
{
lean_object* v_addr_160_; lean_object* v_addr_161_; uint8_t v___x_162_; 
v_addr_160_ = lean_ctor_get(v_x_153_, 0);
v_addr_161_ = lean_ctor_get(v_x_154_, 0);
v___x_162_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_addr_160_, v_addr_161_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr_decEq___boxed(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_163_, v_x_164_);
lean_dec_ref(v_x_164_);
lean_dec_ref(v_x_163_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPAddr(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint8_t v___x_169_; 
v___x_169_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_167_, v_x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr___boxed(lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Std_Net_instDecidableEqIPAddr(v_x_170_, v_x_171_);
lean_dec_ref(v_x_171_);
lean_dec_ref(v_x_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx(lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_unsigned_to_nat(0u);
return v___x_175_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_unsigned_to_nat(1u);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx___boxed(lean_object* v_x_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Net_SocketAddress_ctorIdx(v_x_177_);
lean_dec_ref(v_x_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___redArg(lean_object* v_t_179_, lean_object* v_k_180_){
_start:
{
lean_object* v_addr_181_; lean_object* v___x_182_; 
v_addr_181_ = lean_ctor_get(v_t_179_, 0);
lean_inc_ref(v_addr_181_);
lean_dec_ref(v_t_179_);
v___x_182_ = lean_apply_1(v_k_180_, v_addr_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim(lean_object* v_motive_183_, lean_object* v_ctorIdx_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_k_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_185_, v_k_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___boxed(lean_object* v_motive_189_, lean_object* v_ctorIdx_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_k_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Net_SocketAddress_ctorElim(v_motive_189_, v_ctorIdx_190_, v_t_191_, v_h_192_, v_k_193_);
lean_dec(v_ctorIdx_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim___redArg(lean_object* v_t_195_, lean_object* v_v4_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_195_, v_v4_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_v4_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_199_, v_v4_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim___redArg(lean_object* v_t_203_, lean_object* v_v6_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_203_, v_v6_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim(lean_object* v_motive_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_v6_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_207_, v_v6_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress_default___closed__0(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = l_Std_Net_instInhabitedSocketAddressV4_default;
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress_default(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&l_Std_Net_instInhabitedSocketAddress_default___closed__0, &l_Std_Net_instInhabitedSocketAddress_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddress_default___closed__0);
return v___x_213_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_Net_instInhabitedSocketAddress_default;
return v___x_214_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddress_decEq(lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v_addr_217_; lean_object* v_addr_218_; uint8_t v___x_219_; 
v_addr_217_ = lean_ctor_get(v_x_215_, 0);
v_addr_218_ = lean_ctor_get(v_x_216_, 0);
v___x_219_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_addr_217_, v_addr_218_);
return v___x_219_;
}
else
{
uint8_t v___x_220_; 
v___x_220_ = 0;
return v___x_220_;
}
}
else
{
if (lean_obj_tag(v_x_216_) == 0)
{
uint8_t v___x_221_; 
v___x_221_ = 0;
return v___x_221_;
}
else
{
lean_object* v_addr_222_; lean_object* v_addr_223_; uint8_t v___x_224_; 
v_addr_222_ = lean_ctor_get(v_x_215_, 0);
v_addr_223_ = lean_ctor_get(v_x_216_, 0);
v___x_224_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_addr_222_, v_addr_223_);
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress_decEq___boxed(lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_225_, v_x_226_);
lean_dec_ref(v_x_226_);
lean_dec_ref(v_x_225_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddress(lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
uint8_t v___x_231_; 
v___x_231_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_229_, v_x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress___boxed(lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_Std_Net_instDecidableEqSocketAddress(v_x_232_, v_x_233_);
lean_dec_ref(v_x_233_);
lean_dec_ref(v_x_232_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx(uint8_t v_x_236_){
_start:
{
if (v_x_236_ == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(0u);
return v___x_237_;
}
else
{
lean_object* v___x_238_; 
v___x_238_ = lean_unsigned_to_nat(1u);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx___boxed(lean_object* v_x_239_){
_start:
{
uint8_t v_x_boxed_240_; lean_object* v_res_241_; 
v_x_boxed_240_ = lean_unbox(v_x_239_);
v_res_241_ = l_Std_Net_AddressFamily_ctorIdx(v_x_boxed_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg(lean_object* v_k_242_){
_start:
{
lean_inc(v_k_242_);
return v_k_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg___boxed(lean_object* v_k_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_Net_AddressFamily_ctorElim___redArg(v_k_243_);
lean_dec(v_k_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim(lean_object* v_motive_245_, lean_object* v_ctorIdx_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_k_249_){
_start:
{
lean_inc(v_k_249_);
return v_k_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___boxed(lean_object* v_motive_250_, lean_object* v_ctorIdx_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_k_254_){
_start:
{
uint8_t v_t_boxed_255_; lean_object* v_res_256_; 
v_t_boxed_255_ = lean_unbox(v_t_252_);
v_res_256_ = l_Std_Net_AddressFamily_ctorElim(v_motive_250_, v_ctorIdx_251_, v_t_boxed_255_, v_h_253_, v_k_254_);
lean_dec(v_k_254_);
lean_dec(v_ctorIdx_251_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg(lean_object* v_ipv4_257_){
_start:
{
lean_inc(v_ipv4_257_);
return v_ipv4_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg___boxed(lean_object* v_ipv4_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Net_AddressFamily_ipv4_elim___redArg(v_ipv4_258_);
lean_dec(v_ipv4_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim(lean_object* v_motive_260_, uint8_t v_t_261_, lean_object* v_h_262_, lean_object* v_ipv4_263_){
_start:
{
lean_inc(v_ipv4_263_);
return v_ipv4_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___boxed(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_ipv4_267_){
_start:
{
uint8_t v_t_boxed_268_; lean_object* v_res_269_; 
v_t_boxed_268_ = lean_unbox(v_t_265_);
v_res_269_ = l_Std_Net_AddressFamily_ipv4_elim(v_motive_264_, v_t_boxed_268_, v_h_266_, v_ipv4_267_);
lean_dec(v_ipv4_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg(lean_object* v_ipv6_270_){
_start:
{
lean_inc(v_ipv6_270_);
return v_ipv6_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg___boxed(lean_object* v_ipv6_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Net_AddressFamily_ipv6_elim___redArg(v_ipv6_271_);
lean_dec(v_ipv6_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim(lean_object* v_motive_273_, uint8_t v_t_274_, lean_object* v_h_275_, lean_object* v_ipv6_276_){
_start:
{
lean_inc(v_ipv6_276_);
return v_ipv6_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___boxed(lean_object* v_motive_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_ipv6_280_){
_start:
{
uint8_t v_t_boxed_281_; lean_object* v_res_282_; 
v_t_boxed_281_ = lean_unbox(v_t_278_);
v_res_282_ = l_Std_Net_AddressFamily_ipv6_elim(v_motive_277_, v_t_boxed_281_, v_h_279_, v_ipv6_280_);
lean_dec(v_ipv6_280_);
return v_res_282_;
}
}
static uint8_t _init_l_Std_Net_instInhabitedAddressFamily_default(void){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
}
static uint8_t _init_l_Std_Net_instInhabitedAddressFamily(void){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = 0;
return v___x_284_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_AddressFamily_ofNat(lean_object* v_n_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_nat_dec_le(v_n_285_, v___x_286_);
if (v___x_287_ == 0)
{
uint8_t v___x_288_; 
v___x_288_ = 1;
return v___x_288_;
}
else
{
uint8_t v___x_289_; 
v___x_289_ = 0;
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ofNat___boxed(lean_object* v_n_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Std_Net_AddressFamily_ofNat(v_n_290_);
lean_dec(v_n_290_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqAddressFamily(uint8_t v_x_293_, uint8_t v_y_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = l_Std_Net_AddressFamily_ctorIdx(v_x_293_);
v___x_296_ = l_Std_Net_AddressFamily_ctorIdx(v_y_294_);
v___x_297_ = lean_nat_dec_eq(v___x_295_, v___x_296_);
lean_dec(v___x_296_);
lean_dec(v___x_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqAddressFamily___boxed(lean_object* v_x_298_, lean_object* v_y_299_){
_start:
{
uint8_t v_x_13__boxed_300_; uint8_t v_y_14__boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_x_13__boxed_300_ = lean_unbox(v_x_298_);
v_y_14__boxed_301_ = lean_unbox(v_y_299_);
v_res_302_ = l_Std_Net_instDecidableEqAddressFamily(v_x_13__boxed_300_, v_y_14__boxed_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofParts(uint8_t v_a_304_, uint8_t v_b_305_, uint8_t v_c_306_, uint8_t v_d_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_308_ = lean_unsigned_to_nat(4u);
v___x_309_ = lean_mk_empty_array_with_capacity(v___x_308_);
v___x_310_ = lean_box(v_a_304_);
v___x_311_ = lean_array_push(v___x_309_, v___x_310_);
v___x_312_ = lean_box(v_b_305_);
v___x_313_ = lean_array_push(v___x_311_, v___x_312_);
v___x_314_ = lean_box(v_c_306_);
v___x_315_ = lean_array_push(v___x_313_, v___x_314_);
v___x_316_ = lean_box(v_d_307_);
v___x_317_ = lean_array_push(v___x_315_, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofParts___boxed(lean_object* v_a_318_, lean_object* v_b_319_, lean_object* v_c_320_, lean_object* v_d_321_){
_start:
{
uint8_t v_a_boxed_322_; uint8_t v_b_boxed_323_; uint8_t v_c_boxed_324_; uint8_t v_d_boxed_325_; lean_object* v_res_326_; 
v_a_boxed_322_ = lean_unbox(v_a_318_);
v_b_boxed_323_ = lean_unbox(v_b_319_);
v_c_boxed_324_ = lean_unbox(v_c_320_);
v_d_boxed_325_ = lean_unbox(v_d_321_);
v_res_326_ = l_Std_Net_IPv4Addr_ofParts(v_a_boxed_322_, v_b_boxed_323_, v_c_boxed_324_, v_d_boxed_325_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofString___boxed(lean_object* v_s_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = lean_uv_pton_v4(v_s_328_);
lean_dec_ref(v_s_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_toString___boxed(lean_object* v_addr_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = lean_uv_ntop_v4(v_addr_331_);
lean_dec_ref(v_addr_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_instCoeIPAddr___lam__0(lean_object* v_addr_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v_addr_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instToString___lam__0(lean_object* v_sa_340_){
_start:
{
lean_object* v_addr_341_; uint16_t v_port_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_addr_341_ = lean_ctor_get(v_sa_340_, 0);
v_port_342_ = lean_ctor_get_uint16(v_sa_340_, sizeof(void*)*1);
v___x_343_ = lean_uv_ntop_v4(v_addr_341_);
v___x_344_ = ((lean_object*)(l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0));
v___x_345_ = lean_string_append(v___x_343_, v___x_344_);
v___x_346_ = lean_uint16_to_nat(v_port_342_);
v___x_347_ = l_Nat_reprFast(v___x_346_);
v___x_348_ = lean_string_append(v___x_345_, v___x_347_);
lean_dec_ref(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instToString___lam__0___boxed(lean_object* v_sa_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Net_SocketAddressV4_instToString___lam__0(v_sa_349_);
lean_dec_ref(v_sa_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instCoeSocketAddress___lam__0(lean_object* v_addr_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v_addr_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofParts(uint16_t v_a_357_, uint16_t v_b_358_, uint16_t v_c_359_, uint16_t v_d_360_, uint16_t v_e_361_, uint16_t v_f_362_, uint16_t v_g_363_, uint16_t v_h_364_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_365_ = lean_unsigned_to_nat(8u);
v___x_366_ = lean_mk_empty_array_with_capacity(v___x_365_);
v___x_367_ = lean_box(v_a_357_);
v___x_368_ = lean_array_push(v___x_366_, v___x_367_);
v___x_369_ = lean_box(v_b_358_);
v___x_370_ = lean_array_push(v___x_368_, v___x_369_);
v___x_371_ = lean_box(v_c_359_);
v___x_372_ = lean_array_push(v___x_370_, v___x_371_);
v___x_373_ = lean_box(v_d_360_);
v___x_374_ = lean_array_push(v___x_372_, v___x_373_);
v___x_375_ = lean_box(v_e_361_);
v___x_376_ = lean_array_push(v___x_374_, v___x_375_);
v___x_377_ = lean_box(v_f_362_);
v___x_378_ = lean_array_push(v___x_376_, v___x_377_);
v___x_379_ = lean_box(v_g_363_);
v___x_380_ = lean_array_push(v___x_378_, v___x_379_);
v___x_381_ = lean_box(v_h_364_);
v___x_382_ = lean_array_push(v___x_380_, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofParts___boxed(lean_object* v_a_383_, lean_object* v_b_384_, lean_object* v_c_385_, lean_object* v_d_386_, lean_object* v_e_387_, lean_object* v_f_388_, lean_object* v_g_389_, lean_object* v_h_390_){
_start:
{
uint16_t v_a_boxed_391_; uint16_t v_b_boxed_392_; uint16_t v_c_boxed_393_; uint16_t v_d_boxed_394_; uint16_t v_e_boxed_395_; uint16_t v_f_boxed_396_; uint16_t v_g_boxed_397_; uint16_t v_h_boxed_398_; lean_object* v_res_399_; 
v_a_boxed_391_ = lean_unbox(v_a_383_);
v_b_boxed_392_ = lean_unbox(v_b_384_);
v_c_boxed_393_ = lean_unbox(v_c_385_);
v_d_boxed_394_ = lean_unbox(v_d_386_);
v_e_boxed_395_ = lean_unbox(v_e_387_);
v_f_boxed_396_ = lean_unbox(v_f_388_);
v_g_boxed_397_ = lean_unbox(v_g_389_);
v_h_boxed_398_ = lean_unbox(v_h_390_);
v_res_399_ = l_Std_Net_IPv6Addr_ofParts(v_a_boxed_391_, v_b_boxed_392_, v_c_boxed_393_, v_d_boxed_394_, v_e_boxed_395_, v_f_boxed_396_, v_g_boxed_397_, v_h_boxed_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofString___boxed(lean_object* v_s_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = lean_uv_pton_v6(v_s_401_);
lean_dec_ref(v_s_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_toString___boxed(lean_object* v_addr_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = lean_uv_ntop_v6(v_addr_404_);
lean_dec_ref(v_addr_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_instCoeIPAddr___lam__0(lean_object* v_addr_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v_addr_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instToString___lam__0(lean_object* v_sa_414_){
_start:
{
lean_object* v_addr_415_; uint16_t v_port_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_addr_415_ = lean_ctor_get(v_sa_414_, 0);
v_port_416_ = lean_ctor_get_uint16(v_sa_414_, sizeof(void*)*1);
v___x_417_ = ((lean_object*)(l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0));
v___x_418_ = lean_uv_ntop_v6(v_addr_415_);
v___x_419_ = lean_string_append(v___x_417_, v___x_418_);
lean_dec_ref(v___x_418_);
v___x_420_ = ((lean_object*)(l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1));
v___x_421_ = lean_string_append(v___x_419_, v___x_420_);
v___x_422_ = lean_uint16_to_nat(v_port_416_);
v___x_423_ = l_Nat_reprFast(v___x_422_);
v___x_424_ = lean_string_append(v___x_421_, v___x_423_);
lean_dec_ref(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instToString___lam__0___boxed(lean_object* v_sa_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_Net_SocketAddressV6_instToString___lam__0(v_sa_425_);
lean_dec_ref(v_sa_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instCoeSocketAddress___lam__0(lean_object* v_addr_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v_addr_429_);
return v___x_430_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_IPAddr_family(lean_object* v_x_433_){
_start:
{
if (lean_obj_tag(v_x_433_) == 0)
{
uint8_t v___x_434_; 
v___x_434_ = 0;
return v___x_434_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = 1;
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_family___boxed(lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Std_Net_IPAddr_family(v_x_436_);
lean_dec_ref(v_x_436_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_toString(lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v_addr_440_; lean_object* v___x_441_; 
v_addr_440_ = lean_ctor_get(v_x_439_, 0);
v___x_441_ = lean_uv_ntop_v4(v_addr_440_);
return v___x_441_;
}
else
{
lean_object* v_addr_442_; lean_object* v___x_443_; 
v_addr_442_ = lean_ctor_get(v_x_439_, 0);
v___x_443_ = lean_uv_ntop_v6(v_addr_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_toString___boxed(lean_object* v_x_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_Net_IPAddr_toString(v_x_444_);
lean_dec_ref(v_x_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_instToString___lam__0(lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_object* v_addr_449_; lean_object* v_addr_450_; uint16_t v_port_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_addr_449_ = lean_ctor_get(v_x_448_, 0);
v_addr_450_ = lean_ctor_get(v_addr_449_, 0);
v_port_451_ = lean_ctor_get_uint16(v_addr_449_, sizeof(void*)*1);
v___x_452_ = lean_uv_ntop_v4(v_addr_450_);
v___x_453_ = ((lean_object*)(l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0));
v___x_454_ = lean_string_append(v___x_452_, v___x_453_);
v___x_455_ = lean_uint16_to_nat(v_port_451_);
v___x_456_ = l_Nat_reprFast(v___x_455_);
v___x_457_ = lean_string_append(v___x_454_, v___x_456_);
lean_dec_ref(v___x_456_);
return v___x_457_;
}
else
{
lean_object* v_addr_458_; lean_object* v_addr_459_; uint16_t v_port_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_addr_458_ = lean_ctor_get(v_x_448_, 0);
v_addr_459_ = lean_ctor_get(v_addr_458_, 0);
v_port_460_ = lean_ctor_get_uint16(v_addr_458_, sizeof(void*)*1);
v___x_461_ = ((lean_object*)(l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0));
v___x_462_ = lean_uv_ntop_v6(v_addr_459_);
v___x_463_ = lean_string_append(v___x_461_, v___x_462_);
lean_dec_ref(v___x_462_);
v___x_464_ = ((lean_object*)(l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1));
v___x_465_ = lean_string_append(v___x_463_, v___x_464_);
v___x_466_ = lean_uint16_to_nat(v_port_460_);
v___x_467_ = l_Nat_reprFast(v___x_466_);
v___x_468_ = lean_string_append(v___x_465_, v___x_467_);
lean_dec_ref(v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_instToString___lam__0___boxed(lean_object* v_x_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Net_SocketAddress_instToString___lam__0(v_x_469_);
lean_dec_ref(v_x_469_);
return v_res_470_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_SocketAddress_family(lean_object* v_x_473_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
uint8_t v___x_474_; 
v___x_474_ = 0;
return v___x_474_;
}
else
{
uint8_t v___x_475_; 
v___x_475_ = 1;
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_family___boxed(lean_object* v_x_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Std_Net_SocketAddress_family(v_x_476_);
lean_dec_ref(v_x_476_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ipAddr(lean_object* v_x_479_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
lean_object* v_addr_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_488_; 
v_addr_480_ = lean_ctor_get(v_x_479_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_488_ == 0)
{
v___x_482_ = v_x_479_;
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_addr_480_);
lean_dec(v_x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_addr_484_; lean_object* v___x_486_; 
v_addr_484_ = lean_ctor_get(v_addr_480_, 0);
lean_inc_ref(v_addr_484_);
lean_dec_ref(v_addr_480_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v_addr_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_addr_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
else
{
lean_object* v_addr_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_497_; 
v_addr_489_ = lean_ctor_get(v_x_479_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_497_ == 0)
{
v___x_491_ = v_x_479_;
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_addr_489_);
lean_dec(v_x_479_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_addr_493_; lean_object* v___x_495_; 
v_addr_493_ = lean_ctor_get(v_addr_489_, 0);
lean_inc_ref(v_addr_493_);
lean_dec_ref(v_addr_489_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v_addr_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_addr_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
LEAN_EXPORT uint16_t l_Std_Net_SocketAddress_port(lean_object* v_x_498_){
_start:
{
lean_object* v_addr_499_; uint16_t v_port_500_; 
v_addr_499_ = lean_ctor_get(v_x_498_, 0);
v_port_500_ = lean_ctor_get_uint16(v_addr_499_, sizeof(void*)*1);
return v_port_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_port___boxed(lean_object* v_x_501_){
_start:
{
uint16_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Std_Net_SocketAddress_port(v_x_501_);
lean_dec_ref(v_x_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedInterfaceAddress_default___closed__1(void){
_start:
{
lean_object* v___x_505_; uint8_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_505_ = l_Std_Net_instInhabitedIPAddr_default;
v___x_506_ = 0;
v___x_507_ = l_Std_Net_instInhabitedMACAddr_default;
v___x_508_ = ((lean_object*)(l_Std_Net_instInhabitedInterfaceAddress_default___closed__0));
v___x_509_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
lean_ctor_set(v___x_509_, 2, v___x_505_);
lean_ctor_set(v___x_509_, 3, v___x_505_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*4, v___x_506_);
return v___x_509_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedInterfaceAddress_default(void){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_obj_once(&l_Std_Net_instInhabitedInterfaceAddress_default___closed__1, &l_Std_Net_instInhabitedInterfaceAddress_default___closed__1_once, _init_l_Std_Net_instInhabitedInterfaceAddress_default___closed__1);
return v___x_510_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedInterfaceAddress(void){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_Net_instInhabitedInterfaceAddress_default;
return v___x_511_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqInterfaceAddress_decEq(lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v_name_514_; lean_object* v_physicalAddress_515_; uint8_t v_isLoopback_516_; lean_object* v_address_517_; lean_object* v_netMask_518_; lean_object* v_name_519_; lean_object* v_physicalAddress_520_; uint8_t v_isLoopback_521_; lean_object* v_address_522_; lean_object* v_netMask_523_; uint8_t v___x_527_; 
v_name_514_ = lean_ctor_get(v_x_512_, 0);
v_physicalAddress_515_ = lean_ctor_get(v_x_512_, 1);
v_isLoopback_516_ = lean_ctor_get_uint8(v_x_512_, sizeof(void*)*4);
v_address_517_ = lean_ctor_get(v_x_512_, 2);
v_netMask_518_ = lean_ctor_get(v_x_512_, 3);
v_name_519_ = lean_ctor_get(v_x_513_, 0);
v_physicalAddress_520_ = lean_ctor_get(v_x_513_, 1);
v_isLoopback_521_ = lean_ctor_get_uint8(v_x_513_, sizeof(void*)*4);
v_address_522_ = lean_ctor_get(v_x_513_, 2);
v_netMask_523_ = lean_ctor_get(v_x_513_, 3);
v___x_527_ = lean_string_dec_eq(v_name_514_, v_name_519_);
if (v___x_527_ == 0)
{
return v___x_527_;
}
else
{
uint8_t v___x_528_; 
v___x_528_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_physicalAddress_515_, v_physicalAddress_520_);
if (v___x_528_ == 0)
{
return v___x_528_;
}
else
{
if (v_isLoopback_516_ == 0)
{
if (v_isLoopback_521_ == 0)
{
goto v___jp_524_;
}
else
{
return v_isLoopback_516_;
}
}
else
{
if (v_isLoopback_521_ == 0)
{
return v_isLoopback_521_;
}
else
{
goto v___jp_524_;
}
}
}
}
v___jp_524_:
{
uint8_t v___x_525_; 
v___x_525_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_address_517_, v_address_522_);
if (v___x_525_ == 0)
{
return v___x_525_;
}
else
{
uint8_t v___x_526_; 
v___x_526_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_netMask_518_, v_netMask_523_);
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress_decEq___boxed(lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
uint8_t v_res_531_; lean_object* v_r_532_; 
v_res_531_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_529_, v_x_530_);
lean_dec_ref(v_x_530_);
lean_dec_ref(v_x_529_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqInterfaceAddress(lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
uint8_t v___x_535_; 
v___x_535_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_533_, v_x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress___boxed(lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
uint8_t v_res_538_; lean_object* v_r_539_; 
v_res_538_ = l_Std_Net_instDecidableEqInterfaceAddress(v_x_536_, v_x_537_);
lean_dec_ref(v_x_537_);
lean_dec_ref(v_x_536_);
v_r_539_ = lean_box(v_res_538_);
return v_r_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_interfaceAddresses___boxed(lean_object* v_a_00___x40___internal___hyg_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = lean_uv_interface_addresses();
return v_res_542_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Net_Addr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Net_instInhabitedMACAddr_default = _init_l_Std_Net_instInhabitedMACAddr_default();
lean_mark_persistent(l_Std_Net_instInhabitedMACAddr_default);
l_Std_Net_instInhabitedMACAddr = _init_l_Std_Net_instInhabitedMACAddr();
lean_mark_persistent(l_Std_Net_instInhabitedMACAddr);
l_Std_Net_instInhabitedIPv4Addr_default = _init_l_Std_Net_instInhabitedIPv4Addr_default();
lean_mark_persistent(l_Std_Net_instInhabitedIPv4Addr_default);
l_Std_Net_instInhabitedIPv4Addr = _init_l_Std_Net_instInhabitedIPv4Addr();
lean_mark_persistent(l_Std_Net_instInhabitedIPv4Addr);
l_Std_Net_instInhabitedSocketAddressV4_default = _init_l_Std_Net_instInhabitedSocketAddressV4_default();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV4_default);
l_Std_Net_instInhabitedSocketAddressV4 = _init_l_Std_Net_instInhabitedSocketAddressV4();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV4);
l_Std_Net_instInhabitedIPv6Addr_default = _init_l_Std_Net_instInhabitedIPv6Addr_default();
lean_mark_persistent(l_Std_Net_instInhabitedIPv6Addr_default);
l_Std_Net_instInhabitedIPv6Addr = _init_l_Std_Net_instInhabitedIPv6Addr();
lean_mark_persistent(l_Std_Net_instInhabitedIPv6Addr);
l_Std_Net_instInhabitedSocketAddressV6_default = _init_l_Std_Net_instInhabitedSocketAddressV6_default();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV6_default);
l_Std_Net_instInhabitedSocketAddressV6 = _init_l_Std_Net_instInhabitedSocketAddressV6();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV6);
l_Std_Net_instInhabitedIPAddr_default = _init_l_Std_Net_instInhabitedIPAddr_default();
lean_mark_persistent(l_Std_Net_instInhabitedIPAddr_default);
l_Std_Net_instInhabitedIPAddr = _init_l_Std_Net_instInhabitedIPAddr();
lean_mark_persistent(l_Std_Net_instInhabitedIPAddr);
l_Std_Net_instInhabitedSocketAddress_default = _init_l_Std_Net_instInhabitedSocketAddress_default();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddress_default);
l_Std_Net_instInhabitedSocketAddress = _init_l_Std_Net_instInhabitedSocketAddress();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddress);
l_Std_Net_instInhabitedAddressFamily_default = _init_l_Std_Net_instInhabitedAddressFamily_default();
l_Std_Net_instInhabitedAddressFamily = _init_l_Std_Net_instInhabitedAddressFamily();
l_Std_Net_instInhabitedInterfaceAddress_default = _init_l_Std_Net_instInhabitedInterfaceAddress_default();
lean_mark_persistent(l_Std_Net_instInhabitedInterfaceAddress_default);
l_Std_Net_instInhabitedInterfaceAddress = _init_l_Std_Net_instInhabitedInterfaceAddress();
lean_mark_persistent(l_Std_Net_instInhabitedInterfaceAddress);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Net_Addr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Net_Addr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Net_Addr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Net_Addr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Net_Addr(builtin);
}
#ifdef __cplusplus
}
#endif
