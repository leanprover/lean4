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
uint8_t l_Std_Net_instDecidableEqMACAddr_decEq(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_alloc_closure((void*)(l_instDecidableEqUInt8___boxed), 2, 0);
v___x_10_ = l_Array_instDecidableEqImpl___redArg(v___x_9_, v_x_7_, v_x_8_);
return v___x_10_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqMACAddr_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_7_ = stack[0].m_obj;
lean_object* v_x_8_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_x_7_, v_x_8_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqMACAddr_decEq___boxed(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_x_12_, v_x_13_);
lean_dec_ref(v_x_13_);
lean_dec_ref(v_x_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
uint8_t l_Std_Net_instDecidableEqMACAddr(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_x_16_, v_x_17_);
return v___x_18_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqMACAddr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_16_ = stack[0].m_obj;
lean_object* v_x_17_ = stack[1].m_obj;
uint8_t v_res_19_;
v_res_19_ = l_Std_Net_instDecidableEqMACAddr(v_x_16_, v_x_17_);
stack->m_num = v_res_19_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqMACAddr___boxed(lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Std_Net_instDecidableEqMACAddr(v_x_20_, v_x_21_);
lean_dec_ref(v_x_21_);
lean_dec_ref(v_x_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv4Addr_default___closed__0(void){
_start:
{
uint8_t v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_24_ = 0;
v___x_25_ = lean_unsigned_to_nat(4u);
v___x_26_ = lean_box(v___x_24_);
v___x_27_ = lean_mk_array(v___x_25_, v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv4Addr_default(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Std_Net_instInhabitedIPv4Addr_default___closed__0, &l_Std_Net_instInhabitedIPv4Addr_default___closed__0_once, _init_l_Std_Net_instInhabitedIPv4Addr_default___closed__0);
return v___x_28_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv4Addr(void){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_Net_instInhabitedIPv4Addr_default;
return v___x_29_;
}
}
uint8_t l_Std_Net_instDecidableEqIPv4Addr_decEq(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_alloc_closure((void*)(l_instDecidableEqUInt8___boxed), 2, 0);
v___x_33_ = l_Array_instDecidableEqImpl___redArg(v___x_32_, v_x_30_, v_x_31_);
return v___x_33_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqIPv4Addr_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_30_ = stack[0].m_obj;
lean_object* v_x_31_ = stack[1].m_obj;
uint8_t v_res_34_;
v_res_34_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_x_30_, v_x_31_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv4Addr_decEq___boxed(lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_x_35_, v_x_36_);
lean_dec_ref(v_x_36_);
lean_dec_ref(v_x_35_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
uint8_t l_Std_Net_instDecidableEqIPv4Addr(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
uint8_t v___x_41_; 
v___x_41_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_x_39_, v_x_40_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqIPv4Addr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_39_ = stack[0].m_obj;
lean_object* v_x_40_ = stack[1].m_obj;
uint8_t v_res_42_;
v_res_42_ = l_Std_Net_instDecidableEqIPv4Addr(v_x_39_, v_x_40_);
stack->m_num = v_res_42_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv4Addr___boxed(lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Std_Net_instDecidableEqIPv4Addr(v_x_43_, v_x_44_);
lean_dec_ref(v_x_44_);
lean_dec_ref(v_x_43_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0(void){
_start:
{
uint16_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = 0;
v___x_48_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_49_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set_uint16(v___x_49_, sizeof(void*)*1, v___x_47_);
return v___x_49_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV4_default(void){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_obj_once(&l_Std_Net_instInhabitedSocketAddressV4_default___closed__0, &l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV4(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Std_Net_instInhabitedSocketAddressV4_default;
return v___x_51_;
}
}
uint8_t l_Std_Net_instDecidableEqSocketAddressV4_decEq(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_addr_54_; uint16_t v_port_55_; lean_object* v_addr_56_; uint16_t v_port_57_; uint8_t v___x_58_; 
v_addr_54_ = lean_ctor_get(v_x_52_, 0);
v_port_55_ = lean_ctor_get_uint16(v_x_52_, sizeof(void*)*1);
v_addr_56_ = lean_ctor_get(v_x_53_, 0);
v_port_57_ = lean_ctor_get_uint16(v_x_53_, sizeof(void*)*1);
v___x_58_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_addr_54_, v_addr_56_);
if (v___x_58_ == 0)
{
return v___x_58_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = lean_uint16_dec_eq(v_port_55_, v_port_57_);
return v___x_59_;
}
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqSocketAddressV4_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_52_ = stack[0].m_obj;
lean_object* v_x_53_ = stack[1].m_obj;
uint8_t v_res_60_;
v_res_60_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_x_52_, v_x_53_);
stack->m_num = v_res_60_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV4_decEq___boxed(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_x_61_, v_x_62_);
lean_dec_ref(v_x_62_);
lean_dec_ref(v_x_61_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
uint8_t l_Std_Net_instDecidableEqSocketAddressV4(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_x_65_, v_x_66_);
return v___x_67_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqSocketAddressV4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_65_ = stack[0].m_obj;
lean_object* v_x_66_ = stack[1].m_obj;
uint8_t v_res_68_;
v_res_68_ = l_Std_Net_instDecidableEqSocketAddressV4(v_x_65_, v_x_66_);
stack->m_num = v_res_68_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV4___boxed(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Std_Net_instDecidableEqSocketAddressV4(v_x_69_, v_x_70_);
lean_dec_ref(v_x_70_);
lean_dec_ref(v_x_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv6Addr_default___closed__0(void){
_start:
{
uint16_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = 0;
v___x_74_ = lean_unsigned_to_nat(8u);
v___x_75_ = lean_box(v___x_73_);
v___x_76_ = lean_mk_array(v___x_74_, v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv6Addr_default(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Std_Net_instInhabitedIPv6Addr_default___closed__0, &l_Std_Net_instInhabitedIPv6Addr_default___closed__0_once, _init_l_Std_Net_instInhabitedIPv6Addr_default___closed__0);
return v___x_77_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv6Addr(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Std_Net_instInhabitedIPv6Addr_default;
return v___x_78_;
}
}
uint8_t l_Std_Net_instDecidableEqIPv6Addr_decEq(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_alloc_closure((void*)(l_instDecidableEqUInt16___boxed), 2, 0);
v___x_82_ = l_Array_instDecidableEqImpl___redArg(v___x_81_, v_x_79_, v_x_80_);
return v___x_82_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqIPv6Addr_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_79_ = stack[0].m_obj;
lean_object* v_x_80_ = stack[1].m_obj;
uint8_t v_res_83_;
v_res_83_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_x_79_, v_x_80_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv6Addr_decEq___boxed(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_x_84_, v_x_85_);
lean_dec_ref(v_x_85_);
lean_dec_ref(v_x_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
uint8_t l_Std_Net_instDecidableEqIPv6Addr(lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_x_88_, v_x_89_);
return v___x_90_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqIPv6Addr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_88_ = stack[0].m_obj;
lean_object* v_x_89_ = stack[1].m_obj;
uint8_t v_res_91_;
v_res_91_ = l_Std_Net_instDecidableEqIPv6Addr(v_x_88_, v_x_89_);
stack->m_num = v_res_91_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv6Addr___boxed(lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Std_Net_instDecidableEqIPv6Addr(v_x_92_, v_x_93_);
lean_dec_ref(v_x_93_);
lean_dec_ref(v_x_92_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV6_default___closed__0(void){
_start:
{
uint16_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = 0;
v___x_97_ = l_Std_Net_instInhabitedIPv6Addr_default;
v___x_98_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set_uint16(v___x_98_, sizeof(void*)*1, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV6_default(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Std_Net_instInhabitedSocketAddressV6_default___closed__0, &l_Std_Net_instInhabitedSocketAddressV6_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddressV6_default___closed__0);
return v___x_99_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV6(void){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_Net_instInhabitedSocketAddressV6_default;
return v___x_100_;
}
}
uint8_t l_Std_Net_instDecidableEqSocketAddressV6_decEq(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
lean_object* v_addr_103_; uint16_t v_port_104_; lean_object* v_addr_105_; uint16_t v_port_106_; uint8_t v___x_107_; 
v_addr_103_ = lean_ctor_get(v_x_101_, 0);
v_port_104_ = lean_ctor_get_uint16(v_x_101_, sizeof(void*)*1);
v_addr_105_ = lean_ctor_get(v_x_102_, 0);
v_port_106_ = lean_ctor_get_uint16(v_x_102_, sizeof(void*)*1);
v___x_107_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_addr_103_, v_addr_105_);
if (v___x_107_ == 0)
{
return v___x_107_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = lean_uint16_dec_eq(v_port_104_, v_port_106_);
return v___x_108_;
}
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqSocketAddressV6_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_101_ = stack[0].m_obj;
lean_object* v_x_102_ = stack[1].m_obj;
uint8_t v_res_109_;
v_res_109_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_x_101_, v_x_102_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV6_decEq___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_x_110_, v_x_111_);
lean_dec_ref(v_x_111_);
lean_dec_ref(v_x_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
uint8_t l_Std_Net_instDecidableEqSocketAddressV6(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_x_114_, v_x_115_);
return v___x_116_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqSocketAddressV6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_114_ = stack[0].m_obj;
lean_object* v_x_115_ = stack[1].m_obj;
uint8_t v_res_117_;
v_res_117_ = l_Std_Net_instDecidableEqSocketAddressV6(v_x_114_, v_x_115_);
stack->m_num = v_res_117_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV6___boxed(lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Std_Net_instDecidableEqSocketAddressV6(v_x_118_, v_x_119_);
lean_dec_ref(v_x_119_);
lean_dec_ref(v_x_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx___impl(lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_tag_nat(v_x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx___impl___boxed(lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Net_IPAddr_ctorIdx___impl(v_x_124_);
lean_dec_ref(v_x_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___redArg(lean_object* v_t_126_, lean_object* v_k_127_){
_start:
{
lean_object* v_addr_128_; lean_object* v___x_129_; 
v_addr_128_ = lean_ctor_get(v_t_126_, 0);
lean_inc_ref(v_addr_128_);
lean_dec_ref(v_t_126_);
v___x_129_ = lean_apply_1(v_k_127_, v_addr_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim(lean_object* v_motive_130_, lean_object* v_ctorIdx_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_k_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_132_, v_k_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___boxed(lean_object* v_motive_136_, lean_object* v_ctorIdx_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_k_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_Net_IPAddr_ctorElim(v_motive_136_, v_ctorIdx_137_, v_t_138_, v_h_139_, v_k_140_);
lean_dec(v_ctorIdx_137_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim___redArg(lean_object* v_t_142_, lean_object* v_v4_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_142_, v_v4_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim(lean_object* v_motive_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_v4_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_146_, v_v4_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim___redArg(lean_object* v_t_150_, lean_object* v_v6_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_150_, v_v6_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim(lean_object* v_motive_153_, lean_object* v_t_154_, lean_object* v_h_155_, lean_object* v_v6_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_154_, v_v6_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr_default___closed__0(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr_default(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Std_Net_instInhabitedIPAddr_default___closed__0, &l_Std_Net_instInhabitedIPAddr_default___closed__0_once, _init_l_Std_Net_instInhabitedIPAddr_default___closed__0);
return v___x_160_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Std_Net_instInhabitedIPAddr_default;
return v___x_161_;
}
}
uint8_t l_Std_Net_instDecidableEqIPAddr_decEq(lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v_addr_164_; lean_object* v_addr_165_; uint8_t v___x_166_; 
v_addr_164_ = lean_ctor_get(v_x_162_, 0);
v_addr_165_ = lean_ctor_get(v_x_163_, 0);
v___x_166_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_addr_164_, v_addr_165_);
return v___x_166_;
}
else
{
uint8_t v___x_167_; 
v___x_167_ = 0;
return v___x_167_;
}
}
else
{
if (lean_obj_tag(v_x_163_) == 0)
{
uint8_t v___x_168_; 
v___x_168_ = 0;
return v___x_168_;
}
else
{
lean_object* v_addr_169_; lean_object* v_addr_170_; uint8_t v___x_171_; 
v_addr_169_ = lean_ctor_get(v_x_162_, 0);
v_addr_170_ = lean_ctor_get(v_x_163_, 0);
v___x_171_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_addr_169_, v_addr_170_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqIPAddr_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_162_ = stack[0].m_obj;
lean_object* v_x_163_ = stack[1].m_obj;
uint8_t v_res_172_;
v_res_172_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_162_, v_x_163_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr_decEq___boxed(lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_173_, v_x_174_);
lean_dec_ref(v_x_174_);
lean_dec_ref(v_x_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
uint8_t l_Std_Net_instDecidableEqIPAddr(lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_177_, v_x_178_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqIPAddr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_177_ = stack[0].m_obj;
lean_object* v_x_178_ = stack[1].m_obj;
uint8_t v_res_180_;
v_res_180_ = l_Std_Net_instDecidableEqIPAddr(v_x_177_, v_x_178_);
stack->m_num = v_res_180_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr___boxed(lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Std_Net_instDecidableEqIPAddr(v_x_181_, v_x_182_);
lean_dec_ref(v_x_182_);
lean_dec_ref(v_x_181_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx___impl(lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_tag_nat(v_x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx___impl___boxed(lean_object* v_x_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_Net_SocketAddress_ctorIdx___impl(v_x_187_);
lean_dec_ref(v_x_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___redArg(lean_object* v_t_189_, lean_object* v_k_190_){
_start:
{
lean_object* v_addr_191_; lean_object* v___x_192_; 
v_addr_191_ = lean_ctor_get(v_t_189_, 0);
lean_inc_ref(v_addr_191_);
lean_dec_ref(v_t_189_);
v___x_192_ = lean_apply_1(v_k_190_, v_addr_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim(lean_object* v_motive_193_, lean_object* v_ctorIdx_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_k_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_195_, v_k_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___boxed(lean_object* v_motive_199_, lean_object* v_ctorIdx_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_k_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_Net_SocketAddress_ctorElim(v_motive_199_, v_ctorIdx_200_, v_t_201_, v_h_202_, v_k_203_);
lean_dec(v_ctorIdx_200_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim___redArg(lean_object* v_t_205_, lean_object* v_v4_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_205_, v_v4_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim(lean_object* v_motive_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_v4_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_209_, v_v4_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim___redArg(lean_object* v_t_213_, lean_object* v_v6_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_213_, v_v6_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim(lean_object* v_motive_216_, lean_object* v_t_217_, lean_object* v_h_218_, lean_object* v_v6_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_217_, v_v6_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress_default___closed__0(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = l_Std_Net_instInhabitedSocketAddressV4_default;
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress_default(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Std_Net_instInhabitedSocketAddress_default___closed__0, &l_Std_Net_instInhabitedSocketAddress_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddress_default___closed__0);
return v___x_223_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Std_Net_instInhabitedSocketAddress_default;
return v___x_224_;
}
}
uint8_t l_Std_Net_instDecidableEqSocketAddress_decEq(lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v_addr_227_; lean_object* v_addr_228_; uint8_t v___x_229_; 
v_addr_227_ = lean_ctor_get(v_x_225_, 0);
v_addr_228_ = lean_ctor_get(v_x_226_, 0);
v___x_229_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_addr_227_, v_addr_228_);
return v___x_229_;
}
else
{
uint8_t v___x_230_; 
v___x_230_ = 0;
return v___x_230_;
}
}
else
{
if (lean_obj_tag(v_x_226_) == 0)
{
uint8_t v___x_231_; 
v___x_231_ = 0;
return v___x_231_;
}
else
{
lean_object* v_addr_232_; lean_object* v_addr_233_; uint8_t v___x_234_; 
v_addr_232_ = lean_ctor_get(v_x_225_, 0);
v_addr_233_ = lean_ctor_get(v_x_226_, 0);
v___x_234_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_addr_232_, v_addr_233_);
return v___x_234_;
}
}
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqSocketAddress_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_225_ = stack[0].m_obj;
lean_object* v_x_226_ = stack[1].m_obj;
uint8_t v_res_235_;
v_res_235_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_225_, v_x_226_);
stack->m_num = v_res_235_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress_decEq___boxed(lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_236_, v_x_237_);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_x_236_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
uint8_t l_Std_Net_instDecidableEqSocketAddress(lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_240_, v_x_241_);
return v___x_242_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqSocketAddress_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_240_ = stack[0].m_obj;
lean_object* v_x_241_ = stack[1].m_obj;
uint8_t v_res_243_;
v_res_243_ = l_Std_Net_instDecidableEqSocketAddress(v_x_240_, v_x_241_);
stack->m_num = v_res_243_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress___boxed(lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Std_Net_instDecidableEqSocketAddress(v_x_244_, v_x_245_);
lean_dec_ref(v_x_245_);
lean_dec_ref(v_x_244_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
lean_object* l_Std_Net_AddressFamily_ctorIdx___impl(uint8_t v_x_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_box(v_x_248_);
v___x_250_ = lean_obj_tag_nat(v___x_249_);
lean_dec(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT void l_Std_Net_AddressFamily_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_248_ = stack[0].m_num;
lean_object* v_res_251_;
v_res_251_ = l_Std_Net_AddressFamily_ctorIdx___impl(v_x_248_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx___impl___boxed(lean_object* v_x_252_){
_start:
{
uint8_t v_x_4__boxed_253_; lean_object* v_res_254_; 
v_x_4__boxed_253_ = lean_unbox(v_x_252_);
v_res_254_ = l_Std_Net_AddressFamily_ctorIdx___impl(v_x_4__boxed_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg(lean_object* v_k_255_){
_start:
{
lean_inc(v_k_255_);
return v_k_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg___boxed(lean_object* v_k_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Net_AddressFamily_ctorElim___redArg(v_k_256_);
lean_dec(v_k_256_);
return v_res_257_;
}
}
lean_object* l_Std_Net_AddressFamily_ctorElim(lean_object* v_motive_258_, lean_object* v_ctorIdx_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_k_262_){
_start:
{
lean_inc(v_k_262_);
return v_k_262_;
}
}
LEAN_EXPORT void l_Std_Net_AddressFamily_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_259_ = stack[1].m_obj;
uint8_t v_t_260_ = stack[2].m_num;
lean_object* v_k_262_ = stack[4].m_obj;
lean_object* v_res_263_;
v_res_263_ = l_Std_Net_AddressFamily_ctorElim(lean_box(0), v_ctorIdx_259_, v_t_260_, lean_box(0), v_k_262_);
stack->m_obj
 = v_res_263_;
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___boxed(lean_object* v_motive_264_, lean_object* v_ctorIdx_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_k_268_){
_start:
{
uint8_t v_t_boxed_269_; lean_object* v_res_270_; 
v_t_boxed_269_ = lean_unbox(v_t_266_);
v_res_270_ = l_Std_Net_AddressFamily_ctorElim(v_motive_264_, v_ctorIdx_265_, v_t_boxed_269_, v_h_267_, v_k_268_);
lean_dec(v_k_268_);
lean_dec(v_ctorIdx_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg(lean_object* v_ipv4_271_){
_start:
{
lean_inc(v_ipv4_271_);
return v_ipv4_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg___boxed(lean_object* v_ipv4_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Net_AddressFamily_ipv4_elim___redArg(v_ipv4_272_);
lean_dec(v_ipv4_272_);
return v_res_273_;
}
}
lean_object* l_Std_Net_AddressFamily_ipv4_elim(lean_object* v_motive_274_, uint8_t v_t_275_, lean_object* v_h_276_, lean_object* v_ipv4_277_){
_start:
{
lean_inc(v_ipv4_277_);
return v_ipv4_277_;
}
}
LEAN_EXPORT void l_Std_Net_AddressFamily_ipv4_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_275_ = stack[1].m_num;
lean_object* v_ipv4_277_ = stack[3].m_obj;
lean_object* v_res_278_;
v_res_278_ = l_Std_Net_AddressFamily_ipv4_elim(lean_box(0), v_t_275_, lean_box(0), v_ipv4_277_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___boxed(lean_object* v_motive_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_ipv4_282_){
_start:
{
uint8_t v_t_boxed_283_; lean_object* v_res_284_; 
v_t_boxed_283_ = lean_unbox(v_t_280_);
v_res_284_ = l_Std_Net_AddressFamily_ipv4_elim(v_motive_279_, v_t_boxed_283_, v_h_281_, v_ipv4_282_);
lean_dec(v_ipv4_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg(lean_object* v_ipv6_285_){
_start:
{
lean_inc(v_ipv6_285_);
return v_ipv6_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg___boxed(lean_object* v_ipv6_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_Net_AddressFamily_ipv6_elim___redArg(v_ipv6_286_);
lean_dec(v_ipv6_286_);
return v_res_287_;
}
}
lean_object* l_Std_Net_AddressFamily_ipv6_elim(lean_object* v_motive_288_, uint8_t v_t_289_, lean_object* v_h_290_, lean_object* v_ipv6_291_){
_start:
{
lean_inc(v_ipv6_291_);
return v_ipv6_291_;
}
}
LEAN_EXPORT void l_Std_Net_AddressFamily_ipv6_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_289_ = stack[1].m_num;
lean_object* v_ipv6_291_ = stack[3].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Std_Net_AddressFamily_ipv6_elim(lean_box(0), v_t_289_, lean_box(0), v_ipv6_291_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___boxed(lean_object* v_motive_293_, lean_object* v_t_294_, lean_object* v_h_295_, lean_object* v_ipv6_296_){
_start:
{
uint8_t v_t_boxed_297_; lean_object* v_res_298_; 
v_t_boxed_297_ = lean_unbox(v_t_294_);
v_res_298_ = l_Std_Net_AddressFamily_ipv6_elim(v_motive_293_, v_t_boxed_297_, v_h_295_, v_ipv6_296_);
lean_dec(v_ipv6_296_);
return v_res_298_;
}
}
static uint8_t _init_l_Std_Net_instInhabitedAddressFamily_default(void){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = 0;
return v___x_299_;
}
}
static uint8_t _init_l_Std_Net_instInhabitedAddressFamily(void){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = 0;
return v___x_300_;
}
}
uint8_t l_Std_Net_AddressFamily_ofNat(lean_object* v_n_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_nat_dec_le(v_n_301_, v___x_302_);
if (v___x_303_ == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 1;
return v___x_304_;
}
else
{
uint8_t v___x_305_; 
v___x_305_ = 0;
return v___x_305_;
}
}
}
LEAN_EXPORT void l_Std_Net_AddressFamily_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_301_ = stack[0].m_obj;
uint8_t v_res_306_;
v_res_306_ = l_Std_Net_AddressFamily_ofNat(v_n_301_);
stack->m_num = v_res_306_;
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ofNat___boxed(lean_object* v_n_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_Std_Net_AddressFamily_ofNat(v_n_307_);
lean_dec(v_n_307_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
uint8_t l_Std_Net_instDecidableEqAddressFamily(uint8_t v_x_310_, uint8_t v_y_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_312_ = lean_box(v_x_310_);
v___x_313_ = lean_obj_tag_nat(v___x_312_);
lean_dec(v___x_312_);
v___x_314_ = lean_box(v_y_311_);
v___x_315_ = lean_obj_tag_nat(v___x_314_);
lean_dec(v___x_314_);
v___x_316_ = lean_nat_dec_eq(v___x_313_, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqAddressFamily_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_310_ = stack[0].m_num;
uint8_t v_y_311_ = stack[1].m_num;
uint8_t v_res_317_;
v_res_317_ = l_Std_Net_instDecidableEqAddressFamily(v_x_310_, v_y_311_);
stack->m_num = v_res_317_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqAddressFamily___boxed(lean_object* v_x_318_, lean_object* v_y_319_){
_start:
{
uint8_t v_x_23__boxed_320_; uint8_t v_y_24__boxed_321_; uint8_t v_res_322_; lean_object* v_r_323_; 
v_x_23__boxed_320_ = lean_unbox(v_x_318_);
v_y_24__boxed_321_ = lean_unbox(v_y_319_);
v_res_322_ = l_Std_Net_instDecidableEqAddressFamily(v_x_23__boxed_320_, v_y_24__boxed_321_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
lean_object* l_Std_Net_IPv4Addr_ofParts(uint8_t v_a_324_, uint8_t v_b_325_, uint8_t v_c_326_, uint8_t v_d_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_328_ = lean_unsigned_to_nat(4u);
v___x_329_ = lean_mk_empty_array_with_capacity(v___x_328_);
v___x_330_ = lean_box(v_a_324_);
v___x_331_ = lean_array_push(v___x_329_, v___x_330_);
v___x_332_ = lean_box(v_b_325_);
v___x_333_ = lean_array_push(v___x_331_, v___x_332_);
v___x_334_ = lean_box(v_c_326_);
v___x_335_ = lean_array_push(v___x_333_, v___x_334_);
v___x_336_ = lean_box(v_d_327_);
v___x_337_ = lean_array_push(v___x_335_, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT void l_Std_Net_IPv4Addr_ofParts_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_324_ = stack[0].m_num;
uint8_t v_b_325_ = stack[1].m_num;
uint8_t v_c_326_ = stack[2].m_num;
uint8_t v_d_327_ = stack[3].m_num;
lean_object* v_res_338_;
v_res_338_ = l_Std_Net_IPv4Addr_ofParts(v_a_324_, v_b_325_, v_c_326_, v_d_327_);
stack->m_obj
 = v_res_338_;
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofParts___boxed(lean_object* v_a_339_, lean_object* v_b_340_, lean_object* v_c_341_, lean_object* v_d_342_){
_start:
{
uint8_t v_a_boxed_343_; uint8_t v_b_boxed_344_; uint8_t v_c_boxed_345_; uint8_t v_d_boxed_346_; lean_object* v_res_347_; 
v_a_boxed_343_ = lean_unbox(v_a_339_);
v_b_boxed_344_ = lean_unbox(v_b_340_);
v_c_boxed_345_ = lean_unbox(v_c_341_);
v_d_boxed_346_ = lean_unbox(v_d_342_);
v_res_347_ = l_Std_Net_IPv4Addr_ofParts(v_a_boxed_343_, v_b_boxed_344_, v_c_boxed_345_, v_d_boxed_346_);
return v_res_347_;
}
}
LEAN_EXPORT void l_Std_Net_IPv4Addr_ofString_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_348_ = stack[0].m_obj;
lean_object* v_res_349_;
v_res_349_ = lean_uv_pton_v4(v_s_348_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofString___boxed(lean_object* v_s_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = lean_uv_pton_v4(v_s_350_);
lean_dec_ref(v_s_350_);
return v_res_351_;
}
}
LEAN_EXPORT void l_Std_Net_IPv4Addr_toString_0interp(lean_interpreter_value* stack)
{
lean_object* v_addr_352_ = stack[0].m_obj;
lean_object* v_res_353_;
v_res_353_ = lean_uv_ntop_v4(v_addr_352_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_toString___boxed(lean_object* v_addr_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = lean_uv_ntop_v4(v_addr_354_);
lean_dec_ref(v_addr_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_instCoeIPAddr___lam__0(lean_object* v_addr_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v_addr_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instToString___lam__0(lean_object* v_sa_363_){
_start:
{
lean_object* v_addr_364_; uint16_t v_port_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_addr_364_ = lean_ctor_get(v_sa_363_, 0);
v_port_365_ = lean_ctor_get_uint16(v_sa_363_, sizeof(void*)*1);
v___x_366_ = lean_uv_ntop_v4(v_addr_364_);
v___x_367_ = ((lean_object*)(l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0));
v___x_368_ = lean_string_append(v___x_366_, v___x_367_);
v___x_369_ = lean_uint16_to_nat(v_port_365_);
v___x_370_ = l_Nat_reprFast(v___x_369_);
v___x_371_ = lean_string_append(v___x_368_, v___x_370_);
lean_dec_ref(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instToString___lam__0___boxed(lean_object* v_sa_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_Net_SocketAddressV4_instToString___lam__0(v_sa_372_);
lean_dec_ref(v_sa_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instCoeSocketAddress___lam__0(lean_object* v_addr_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v_addr_376_);
return v___x_377_;
}
}
lean_object* l_Std_Net_IPv6Addr_ofParts(uint16_t v_a_380_, uint16_t v_b_381_, uint16_t v_c_382_, uint16_t v_d_383_, uint16_t v_e_384_, uint16_t v_f_385_, uint16_t v_g_386_, uint16_t v_h_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_388_ = lean_unsigned_to_nat(8u);
v___x_389_ = lean_mk_empty_array_with_capacity(v___x_388_);
v___x_390_ = lean_box(v_a_380_);
v___x_391_ = lean_array_push(v___x_389_, v___x_390_);
v___x_392_ = lean_box(v_b_381_);
v___x_393_ = lean_array_push(v___x_391_, v___x_392_);
v___x_394_ = lean_box(v_c_382_);
v___x_395_ = lean_array_push(v___x_393_, v___x_394_);
v___x_396_ = lean_box(v_d_383_);
v___x_397_ = lean_array_push(v___x_395_, v___x_396_);
v___x_398_ = lean_box(v_e_384_);
v___x_399_ = lean_array_push(v___x_397_, v___x_398_);
v___x_400_ = lean_box(v_f_385_);
v___x_401_ = lean_array_push(v___x_399_, v___x_400_);
v___x_402_ = lean_box(v_g_386_);
v___x_403_ = lean_array_push(v___x_401_, v___x_402_);
v___x_404_ = lean_box(v_h_387_);
v___x_405_ = lean_array_push(v___x_403_, v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT void l_Std_Net_IPv6Addr_ofParts_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_380_ = stack[0].m_num;
uint16_t v_b_381_ = stack[1].m_num;
uint16_t v_c_382_ = stack[2].m_num;
uint16_t v_d_383_ = stack[3].m_num;
uint16_t v_e_384_ = stack[4].m_num;
uint16_t v_f_385_ = stack[5].m_num;
uint16_t v_g_386_ = stack[6].m_num;
uint16_t v_h_387_ = stack[7].m_num;
lean_object* v_res_406_;
v_res_406_ = l_Std_Net_IPv6Addr_ofParts(v_a_380_, v_b_381_, v_c_382_, v_d_383_, v_e_384_, v_f_385_, v_g_386_, v_h_387_);
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofParts___boxed(lean_object* v_a_407_, lean_object* v_b_408_, lean_object* v_c_409_, lean_object* v_d_410_, lean_object* v_e_411_, lean_object* v_f_412_, lean_object* v_g_413_, lean_object* v_h_414_){
_start:
{
uint16_t v_a_boxed_415_; uint16_t v_b_boxed_416_; uint16_t v_c_boxed_417_; uint16_t v_d_boxed_418_; uint16_t v_e_boxed_419_; uint16_t v_f_boxed_420_; uint16_t v_g_boxed_421_; uint16_t v_h_boxed_422_; lean_object* v_res_423_; 
v_a_boxed_415_ = lean_unbox(v_a_407_);
v_b_boxed_416_ = lean_unbox(v_b_408_);
v_c_boxed_417_ = lean_unbox(v_c_409_);
v_d_boxed_418_ = lean_unbox(v_d_410_);
v_e_boxed_419_ = lean_unbox(v_e_411_);
v_f_boxed_420_ = lean_unbox(v_f_412_);
v_g_boxed_421_ = lean_unbox(v_g_413_);
v_h_boxed_422_ = lean_unbox(v_h_414_);
v_res_423_ = l_Std_Net_IPv6Addr_ofParts(v_a_boxed_415_, v_b_boxed_416_, v_c_boxed_417_, v_d_boxed_418_, v_e_boxed_419_, v_f_boxed_420_, v_g_boxed_421_, v_h_boxed_422_);
return v_res_423_;
}
}
LEAN_EXPORT void l_Std_Net_IPv6Addr_ofString_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_424_ = stack[0].m_obj;
lean_object* v_res_425_;
v_res_425_ = lean_uv_pton_v6(v_s_424_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofString___boxed(lean_object* v_s_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = lean_uv_pton_v6(v_s_426_);
lean_dec_ref(v_s_426_);
return v_res_427_;
}
}
LEAN_EXPORT void l_Std_Net_IPv6Addr_toString_0interp(lean_interpreter_value* stack)
{
lean_object* v_addr_428_ = stack[0].m_obj;
lean_object* v_res_429_;
v_res_429_ = lean_uv_ntop_v6(v_addr_428_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_toString___boxed(lean_object* v_addr_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = lean_uv_ntop_v6(v_addr_430_);
lean_dec_ref(v_addr_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_instCoeIPAddr___lam__0(lean_object* v_addr_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v_addr_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instToString___lam__0(lean_object* v_sa_440_){
_start:
{
lean_object* v_addr_441_; uint16_t v_port_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_addr_441_ = lean_ctor_get(v_sa_440_, 0);
v_port_442_ = lean_ctor_get_uint16(v_sa_440_, sizeof(void*)*1);
v___x_443_ = ((lean_object*)(l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0));
v___x_444_ = lean_uv_ntop_v6(v_addr_441_);
v___x_445_ = lean_string_append(v___x_443_, v___x_444_);
lean_dec_ref(v___x_444_);
v___x_446_ = ((lean_object*)(l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1));
v___x_447_ = lean_string_append(v___x_445_, v___x_446_);
v___x_448_ = lean_uint16_to_nat(v_port_442_);
v___x_449_ = l_Nat_reprFast(v___x_448_);
v___x_450_ = lean_string_append(v___x_447_, v___x_449_);
lean_dec_ref(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instToString___lam__0___boxed(lean_object* v_sa_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_Net_SocketAddressV6_instToString___lam__0(v_sa_451_);
lean_dec_ref(v_sa_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instCoeSocketAddress___lam__0(lean_object* v_addr_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v_addr_455_);
return v___x_456_;
}
}
uint8_t l_Std_Net_IPAddr_family(lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
uint8_t v___x_460_; 
v___x_460_ = 0;
return v___x_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 1;
return v___x_461_;
}
}
}
LEAN_EXPORT void l_Std_Net_IPAddr_family_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_459_ = stack[0].m_obj;
uint8_t v_res_462_;
v_res_462_ = l_Std_Net_IPAddr_family(v_x_459_);
stack->m_num = v_res_462_;
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_family___boxed(lean_object* v_x_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_Std_Net_IPAddr_family(v_x_463_);
lean_dec_ref(v_x_463_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_toString(lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v_addr_467_; lean_object* v___x_468_; 
v_addr_467_ = lean_ctor_get(v_x_466_, 0);
v___x_468_ = lean_uv_ntop_v4(v_addr_467_);
return v___x_468_;
}
else
{
lean_object* v_addr_469_; lean_object* v___x_470_; 
v_addr_469_ = lean_ctor_get(v_x_466_, 0);
v___x_470_ = lean_uv_ntop_v6(v_addr_469_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_toString___boxed(lean_object* v_x_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_Net_IPAddr_toString(v_x_471_);
lean_dec_ref(v_x_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_instToString___lam__0(lean_object* v_x_475_){
_start:
{
if (lean_obj_tag(v_x_475_) == 0)
{
lean_object* v_addr_476_; lean_object* v_addr_477_; uint16_t v_port_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_addr_476_ = lean_ctor_get(v_x_475_, 0);
v_addr_477_ = lean_ctor_get(v_addr_476_, 0);
v_port_478_ = lean_ctor_get_uint16(v_addr_476_, sizeof(void*)*1);
v___x_479_ = lean_uv_ntop_v4(v_addr_477_);
v___x_480_ = ((lean_object*)(l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0));
v___x_481_ = lean_string_append(v___x_479_, v___x_480_);
v___x_482_ = lean_uint16_to_nat(v_port_478_);
v___x_483_ = l_Nat_reprFast(v___x_482_);
v___x_484_ = lean_string_append(v___x_481_, v___x_483_);
lean_dec_ref(v___x_483_);
return v___x_484_;
}
else
{
lean_object* v_addr_485_; lean_object* v_addr_486_; uint16_t v_port_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_addr_485_ = lean_ctor_get(v_x_475_, 0);
v_addr_486_ = lean_ctor_get(v_addr_485_, 0);
v_port_487_ = lean_ctor_get_uint16(v_addr_485_, sizeof(void*)*1);
v___x_488_ = ((lean_object*)(l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0));
v___x_489_ = lean_uv_ntop_v6(v_addr_486_);
v___x_490_ = lean_string_append(v___x_488_, v___x_489_);
lean_dec_ref(v___x_489_);
v___x_491_ = ((lean_object*)(l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1));
v___x_492_ = lean_string_append(v___x_490_, v___x_491_);
v___x_493_ = lean_uint16_to_nat(v_port_487_);
v___x_494_ = l_Nat_reprFast(v___x_493_);
v___x_495_ = lean_string_append(v___x_492_, v___x_494_);
lean_dec_ref(v___x_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_instToString___lam__0___boxed(lean_object* v_x_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_Net_SocketAddress_instToString___lam__0(v_x_496_);
lean_dec_ref(v_x_496_);
return v_res_497_;
}
}
uint8_t l_Std_Net_SocketAddress_family(lean_object* v_x_500_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
uint8_t v___x_501_; 
v___x_501_ = 0;
return v___x_501_;
}
else
{
uint8_t v___x_502_; 
v___x_502_ = 1;
return v___x_502_;
}
}
}
LEAN_EXPORT void l_Std_Net_SocketAddress_family_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_500_ = stack[0].m_obj;
uint8_t v_res_503_;
v_res_503_ = l_Std_Net_SocketAddress_family(v_x_500_);
stack->m_num = v_res_503_;
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_family___boxed(lean_object* v_x_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_Net_SocketAddress_family(v_x_504_);
lean_dec_ref(v_x_504_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ipAddr(lean_object* v_x_507_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v_addr_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
v_addr_508_ = lean_ctor_get(v_x_507_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_507_);
if (v_isSharedCheck_516_ == 0)
{
v___x_510_ = v_x_507_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_addr_508_);
lean_dec(v_x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_addr_512_; lean_object* v___x_514_; 
v_addr_512_ = lean_ctor_get(v_addr_508_, 0);
lean_inc_ref(v_addr_512_);
lean_dec_ref(v_addr_508_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v_addr_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_addr_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_addr_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_addr_517_ = lean_ctor_get(v_x_507_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_507_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v_x_507_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_addr_517_);
lean_dec(v_x_507_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_addr_521_; lean_object* v___x_523_; 
v_addr_521_ = lean_ctor_get(v_addr_517_, 0);
lean_inc_ref(v_addr_521_);
lean_dec_ref(v_addr_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v_addr_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_addr_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
uint16_t l_Std_Net_SocketAddress_port(lean_object* v_x_526_){
_start:
{
lean_object* v_addr_527_; uint16_t v_port_528_; 
v_addr_527_ = lean_ctor_get(v_x_526_, 0);
v_port_528_ = lean_ctor_get_uint16(v_addr_527_, sizeof(void*)*1);
return v_port_528_;
}
}
LEAN_EXPORT void l_Std_Net_SocketAddress_port_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_526_ = stack[0].m_obj;
uint16_t v_res_529_;
v_res_529_ = l_Std_Net_SocketAddress_port(v_x_526_);
stack->m_num = v_res_529_;
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_port___boxed(lean_object* v_x_530_){
_start:
{
uint16_t v_res_531_; lean_object* v_r_532_; 
v_res_531_ = l_Std_Net_SocketAddress_port(v_x_530_);
lean_dec_ref(v_x_530_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedInterfaceAddress_default___closed__1(void){
_start:
{
lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_534_ = l_Std_Net_instInhabitedIPAddr_default;
v___x_535_ = 0;
v___x_536_ = l_Std_Net_instInhabitedMACAddr_default;
v___x_537_ = ((lean_object*)(l_Std_Net_instInhabitedInterfaceAddress_default___closed__0));
v___x_538_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_536_);
lean_ctor_set(v___x_538_, 2, v___x_534_);
lean_ctor_set(v___x_538_, 3, v___x_534_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*4, v___x_535_);
return v___x_538_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedInterfaceAddress_default(void){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Std_Net_instInhabitedInterfaceAddress_default___closed__1, &l_Std_Net_instInhabitedInterfaceAddress_default___closed__1_once, _init_l_Std_Net_instInhabitedInterfaceAddress_default___closed__1);
return v___x_539_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedInterfaceAddress(void){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_Net_instInhabitedInterfaceAddress_default;
return v___x_540_;
}
}
uint8_t l_Std_Net_instDecidableEqInterfaceAddress_decEq(lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v_name_543_; lean_object* v_physicalAddress_544_; uint8_t v_isLoopback_545_; lean_object* v_address_546_; lean_object* v_netMask_547_; lean_object* v_name_548_; lean_object* v_physicalAddress_549_; uint8_t v_isLoopback_550_; lean_object* v_address_551_; lean_object* v_netMask_552_; uint8_t v___y_554_; uint8_t v___x_557_; 
v_name_543_ = lean_ctor_get(v_x_541_, 0);
v_physicalAddress_544_ = lean_ctor_get(v_x_541_, 1);
v_isLoopback_545_ = lean_ctor_get_uint8(v_x_541_, sizeof(void*)*4);
v_address_546_ = lean_ctor_get(v_x_541_, 2);
v_netMask_547_ = lean_ctor_get(v_x_541_, 3);
v_name_548_ = lean_ctor_get(v_x_542_, 0);
v_physicalAddress_549_ = lean_ctor_get(v_x_542_, 1);
v_isLoopback_550_ = lean_ctor_get_uint8(v_x_542_, sizeof(void*)*4);
v_address_551_ = lean_ctor_get(v_x_542_, 2);
v_netMask_552_ = lean_ctor_get(v_x_542_, 3);
v___x_557_ = lean_string_dec_eq(v_name_543_, v_name_548_);
if (v___x_557_ == 0)
{
return v___x_557_;
}
else
{
uint8_t v___x_558_; 
v___x_558_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_physicalAddress_544_, v_physicalAddress_549_);
if (v___x_558_ == 0)
{
return v___x_558_;
}
else
{
if (v_isLoopback_550_ == 0)
{
if (v_isLoopback_545_ == 0)
{
v___y_554_ = v___x_558_;
goto v___jp_553_;
}
else
{
return v_isLoopback_550_;
}
}
else
{
v___y_554_ = v_isLoopback_545_;
goto v___jp_553_;
}
}
}
v___jp_553_:
{
if (v___y_554_ == 0)
{
return v___y_554_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_address_546_, v_address_551_);
if (v___x_555_ == 0)
{
return v___x_555_;
}
else
{
uint8_t v___x_556_; 
v___x_556_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_netMask_547_, v_netMask_552_);
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqInterfaceAddress_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_541_ = stack[0].m_obj;
lean_object* v_x_542_ = stack[1].m_obj;
uint8_t v_res_559_;
v_res_559_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_541_, v_x_542_);
stack->m_num = v_res_559_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress_decEq___boxed(lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_560_, v_x_561_);
lean_dec_ref(v_x_561_);
lean_dec_ref(v_x_560_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
uint8_t l_Std_Net_instDecidableEqInterfaceAddress(lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_564_, v_x_565_);
return v___x_566_;
}
}
LEAN_EXPORT void l_Std_Net_instDecidableEqInterfaceAddress_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_564_ = stack[0].m_obj;
lean_object* v_x_565_ = stack[1].m_obj;
uint8_t v_res_567_;
v_res_567_ = l_Std_Net_instDecidableEqInterfaceAddress(v_x_564_, v_x_565_);
stack->m_num = v_res_567_;
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress___boxed(lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
uint8_t v_res_570_; lean_object* v_r_571_; 
v_res_570_ = l_Std_Net_instDecidableEqInterfaceAddress(v_x_568_, v_x_569_);
lean_dec_ref(v_x_569_);
lean_dec_ref(v_x_568_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT void l_Std_Net_interfaceAddresses_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_573_;
v_res_573_ = lean_uv_interface_addresses();
stack->m_obj
 = v_res_573_;
}
LEAN_EXPORT lean_object* l_Std_Net_interfaceAddresses___boxed(lean_object* v_a_00___x40___internal___hyg_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = lean_uv_interface_addresses();
return v_res_575_;
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
