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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx___impl(lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_tag_nat(v_x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx___impl___boxed(lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Net_IPAddr_ctorIdx___impl(v_x_114_);
lean_dec_ref(v_x_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___redArg(lean_object* v_t_116_, lean_object* v_k_117_){
_start:
{
lean_object* v_addr_118_; lean_object* v___x_119_; 
v_addr_118_ = lean_ctor_get(v_t_116_, 0);
lean_inc_ref(v_addr_118_);
lean_dec_ref(v_t_116_);
v___x_119_ = lean_apply_1(v_k_117_, v_addr_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim(lean_object* v_motive_120_, lean_object* v_ctorIdx_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_k_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_122_, v_k_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___boxed(lean_object* v_motive_126_, lean_object* v_ctorIdx_127_, lean_object* v_t_128_, lean_object* v_h_129_, lean_object* v_k_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_Net_IPAddr_ctorElim(v_motive_126_, v_ctorIdx_127_, v_t_128_, v_h_129_, v_k_130_);
lean_dec(v_ctorIdx_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim___redArg(lean_object* v_t_132_, lean_object* v_v4_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_132_, v_v4_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim(lean_object* v_motive_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_v4_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_136_, v_v4_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim___redArg(lean_object* v_t_140_, lean_object* v_v6_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_140_, v_v6_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim(lean_object* v_motive_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_v6_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_144_, v_v6_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr_default___closed__0(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr_default(void){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_obj_once(&l_Std_Net_instInhabitedIPAddr_default___closed__0, &l_Std_Net_instInhabitedIPAddr_default___closed__0_once, _init_l_Std_Net_instInhabitedIPAddr_default___closed__0);
return v___x_150_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Std_Net_instInhabitedIPAddr_default;
return v___x_151_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPAddr_decEq(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
if (lean_obj_tag(v_x_153_) == 0)
{
lean_object* v_addr_154_; lean_object* v_addr_155_; uint8_t v___x_156_; 
v_addr_154_ = lean_ctor_get(v_x_152_, 0);
v_addr_155_ = lean_ctor_get(v_x_153_, 0);
v___x_156_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_addr_154_, v_addr_155_);
return v___x_156_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
}
else
{
if (lean_obj_tag(v_x_153_) == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
else
{
lean_object* v_addr_159_; lean_object* v_addr_160_; uint8_t v___x_161_; 
v_addr_159_ = lean_ctor_get(v_x_152_, 0);
v_addr_160_ = lean_ctor_get(v_x_153_, 0);
v___x_161_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_addr_159_, v_addr_160_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr_decEq___boxed(lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_162_, v_x_163_);
lean_dec_ref(v_x_163_);
lean_dec_ref(v_x_162_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPAddr(lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_166_, v_x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr___boxed(lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_Net_instDecidableEqIPAddr(v_x_169_, v_x_170_);
lean_dec_ref(v_x_170_);
lean_dec_ref(v_x_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx___impl(lean_object* v_x_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_tag_nat(v_x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx___impl___boxed(lean_object* v_x_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_Net_SocketAddress_ctorIdx___impl(v_x_175_);
lean_dec_ref(v_x_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___redArg(lean_object* v_t_177_, lean_object* v_k_178_){
_start:
{
lean_object* v_addr_179_; lean_object* v___x_180_; 
v_addr_179_ = lean_ctor_get(v_t_177_, 0);
lean_inc_ref(v_addr_179_);
lean_dec_ref(v_t_177_);
v___x_180_ = lean_apply_1(v_k_178_, v_addr_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim(lean_object* v_motive_181_, lean_object* v_ctorIdx_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_k_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_183_, v_k_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___boxed(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Net_SocketAddress_ctorElim(v_motive_187_, v_ctorIdx_188_, v_t_189_, v_h_190_, v_k_191_);
lean_dec(v_ctorIdx_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim___redArg(lean_object* v_t_193_, lean_object* v_v4_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_193_, v_v4_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_v4_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_197_, v_v4_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim___redArg(lean_object* v_t_201_, lean_object* v_v6_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_201_, v_v6_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_v6_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_205_, v_v6_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress_default___closed__0(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = l_Std_Net_instInhabitedSocketAddressV4_default;
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress_default(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&l_Std_Net_instInhabitedSocketAddress_default___closed__0, &l_Std_Net_instInhabitedSocketAddress_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddress_default___closed__0);
return v___x_211_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Std_Net_instInhabitedSocketAddress_default;
return v___x_212_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddress_decEq(lean_object* v_x_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v_addr_215_; lean_object* v_addr_216_; uint8_t v___x_217_; 
v_addr_215_ = lean_ctor_get(v_x_213_, 0);
v_addr_216_ = lean_ctor_get(v_x_214_, 0);
v___x_217_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_addr_215_, v_addr_216_);
return v___x_217_;
}
else
{
uint8_t v___x_218_; 
v___x_218_ = 0;
return v___x_218_;
}
}
else
{
if (lean_obj_tag(v_x_214_) == 0)
{
uint8_t v___x_219_; 
v___x_219_ = 0;
return v___x_219_;
}
else
{
lean_object* v_addr_220_; lean_object* v_addr_221_; uint8_t v___x_222_; 
v_addr_220_ = lean_ctor_get(v_x_213_, 0);
v_addr_221_ = lean_ctor_get(v_x_214_, 0);
v___x_222_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_addr_220_, v_addr_221_);
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress_decEq___boxed(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_223_, v_x_224_);
lean_dec_ref(v_x_224_);
lean_dec_ref(v_x_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddress(lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_227_, v_x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress___boxed(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Std_Net_instDecidableEqSocketAddress(v_x_230_, v_x_231_);
lean_dec_ref(v_x_231_);
lean_dec_ref(v_x_230_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx___impl(uint8_t v_x_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_box(v_x_234_);
v___x_236_ = lean_obj_tag_nat(v___x_235_);
lean_dec(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx___impl___boxed(lean_object* v_x_237_){
_start:
{
uint8_t v_x_4__boxed_238_; lean_object* v_res_239_; 
v_x_4__boxed_238_ = lean_unbox(v_x_237_);
v_res_239_ = l_Std_Net_AddressFamily_ctorIdx___impl(v_x_4__boxed_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg(lean_object* v_k_240_){
_start:
{
lean_inc(v_k_240_);
return v_k_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg___boxed(lean_object* v_k_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Net_AddressFamily_ctorElim___redArg(v_k_241_);
lean_dec(v_k_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim(lean_object* v_motive_243_, lean_object* v_ctorIdx_244_, uint8_t v_t_245_, lean_object* v_h_246_, lean_object* v_k_247_){
_start:
{
lean_inc(v_k_247_);
return v_k_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___boxed(lean_object* v_motive_248_, lean_object* v_ctorIdx_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_k_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Std_Net_AddressFamily_ctorElim(v_motive_248_, v_ctorIdx_249_, v_t_boxed_253_, v_h_251_, v_k_252_);
lean_dec(v_k_252_);
lean_dec(v_ctorIdx_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg(lean_object* v_ipv4_255_){
_start:
{
lean_inc(v_ipv4_255_);
return v_ipv4_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg___boxed(lean_object* v_ipv4_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Net_AddressFamily_ipv4_elim___redArg(v_ipv4_256_);
lean_dec(v_ipv4_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_ipv4_261_){
_start:
{
lean_inc(v_ipv4_261_);
return v_ipv4_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_ipv4_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Std_Net_AddressFamily_ipv4_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_ipv4_265_);
lean_dec(v_ipv4_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg(lean_object* v_ipv6_268_){
_start:
{
lean_inc(v_ipv6_268_);
return v_ipv6_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg___boxed(lean_object* v_ipv6_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Net_AddressFamily_ipv6_elim___redArg(v_ipv6_269_);
lean_dec(v_ipv6_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim(lean_object* v_motive_271_, uint8_t v_t_272_, lean_object* v_h_273_, lean_object* v_ipv6_274_){
_start:
{
lean_inc(v_ipv6_274_);
return v_ipv6_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___boxed(lean_object* v_motive_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_ipv6_278_){
_start:
{
uint8_t v_t_boxed_279_; lean_object* v_res_280_; 
v_t_boxed_279_ = lean_unbox(v_t_276_);
v_res_280_ = l_Std_Net_AddressFamily_ipv6_elim(v_motive_275_, v_t_boxed_279_, v_h_277_, v_ipv6_278_);
lean_dec(v_ipv6_278_);
return v_res_280_;
}
}
static uint8_t _init_l_Std_Net_instInhabitedAddressFamily_default(void){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = 0;
return v___x_281_;
}
}
static uint8_t _init_l_Std_Net_instInhabitedAddressFamily(void){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_AddressFamily_ofNat(lean_object* v_n_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_nat_dec_le(v_n_283_, v___x_284_);
if (v___x_285_ == 0)
{
uint8_t v___x_286_; 
v___x_286_ = 1;
return v___x_286_;
}
else
{
uint8_t v___x_287_; 
v___x_287_ = 0;
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ofNat___boxed(lean_object* v_n_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Std_Net_AddressFamily_ofNat(v_n_288_);
lean_dec(v_n_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqAddressFamily(uint8_t v_x_291_, uint8_t v_y_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_293_ = lean_box(v_x_291_);
v___x_294_ = lean_obj_tag_nat(v___x_293_);
lean_dec(v___x_293_);
v___x_295_ = lean_box(v_y_292_);
v___x_296_ = lean_obj_tag_nat(v___x_295_);
lean_dec(v___x_295_);
v___x_297_ = lean_nat_dec_eq(v___x_294_, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqAddressFamily___boxed(lean_object* v_x_298_, lean_object* v_y_299_){
_start:
{
uint8_t v_x_23__boxed_300_; uint8_t v_y_24__boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_x_23__boxed_300_ = lean_unbox(v_x_298_);
v_y_24__boxed_301_ = lean_unbox(v_y_299_);
v_res_302_ = l_Std_Net_instDecidableEqAddressFamily(v_x_23__boxed_300_, v_y_24__boxed_301_);
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
lean_object* v_name_514_; lean_object* v_physicalAddress_515_; uint8_t v_isLoopback_516_; lean_object* v_address_517_; lean_object* v_netMask_518_; lean_object* v_name_519_; lean_object* v_physicalAddress_520_; uint8_t v_isLoopback_521_; lean_object* v_address_522_; lean_object* v_netMask_523_; uint8_t v___y_525_; uint8_t v___x_528_; 
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
v___x_528_ = lean_string_dec_eq(v_name_514_, v_name_519_);
if (v___x_528_ == 0)
{
return v___x_528_;
}
else
{
uint8_t v___x_529_; 
v___x_529_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_physicalAddress_515_, v_physicalAddress_520_);
if (v___x_529_ == 0)
{
return v___x_529_;
}
else
{
if (v_isLoopback_521_ == 0)
{
if (v_isLoopback_516_ == 0)
{
v___y_525_ = v___x_529_;
goto v___jp_524_;
}
else
{
return v_isLoopback_521_;
}
}
else
{
v___y_525_ = v_isLoopback_516_;
goto v___jp_524_;
}
}
}
v___jp_524_:
{
if (v___y_525_ == 0)
{
return v___y_525_;
}
else
{
uint8_t v___x_526_; 
v___x_526_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_address_517_, v_address_522_);
if (v___x_526_ == 0)
{
return v___x_526_;
}
else
{
uint8_t v___x_527_; 
v___x_527_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_netMask_518_, v_netMask_523_);
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress_decEq___boxed(lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_530_, v_x_531_);
lean_dec_ref(v_x_531_);
lean_dec_ref(v_x_530_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqInterfaceAddress(lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_534_, v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress___boxed(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_Std_Net_instDecidableEqInterfaceAddress(v_x_537_, v_x_538_);
lean_dec_ref(v_x_538_);
lean_dec_ref(v_x_537_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_interfaceAddresses___boxed(lean_object* v_a_00___x40___internal___hyg_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = lean_uv_interface_addresses();
return v_res_543_;
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
