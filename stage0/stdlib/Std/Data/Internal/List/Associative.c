// Lean compiler output
// Module: Std.Data.Internal.List.Associative
// Imports: public import Init.Data.Option.Attach public import Init.Data.List.Perm public import Std.Data.Internal.List.Defs import all Std.Data.Internal.List.Defs public import Init.Data.Order.LemmasExtra public import Init.Data.Bool import Init.ByCases import Init.Data.List.Count import Init.Data.List.Erase import Init.Data.List.Find import Init.Data.List.MinMax import Init.Data.List.Pairwise import Init.Data.List.Sublist import Init.Data.Prod import Init.Omega
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
lean_object* l_Ord_opposite___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_min_x3f___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntryD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_List_getEntry_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Data.Internal.List.Associative"};
static const lean_object* l_Std_Internal_List_getEntry_x21___redArg___closed__0 = (const lean_object*)&l_Std_Internal_List_getEntry_x21___redArg___closed__0_value;
static const lean_string_object l_Std_Internal_List_getEntry_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Std.Internal.List.getEntry!"};
static const lean_object* l_Std_Internal_List_getEntry_x21___redArg___closed__1 = (const lean_object*)&l_Std_Internal_List_getEntry_x21___redArg___closed__1_value;
static const lean_string_object l_Std_Internal_List_getEntry_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "key is not present in associative list"};
static const lean_object* l_Std_Internal_List_getEntry_x21___redArg___closed__2 = (const lean_object*)&l_Std_Internal_List_getEntry_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_Internal_List_getEntry_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_List_getEntry_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_List_getValueCast_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_Internal_List_getValueCast_x21___redArg___closed__0 = (const lean_object*)&l_Std_Internal_List_getValueCast_x21___redArg___closed__0_value;
static const lean_string_object l_Std_Internal_List_getValueCast_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_Internal_List_getValueCast_x21___redArg___closed__1 = (const lean_object*)&l_Std_Internal_List_getValueCast_x21___redArg___closed__1_value;
static const lean_string_object l_Std_Internal_List_getValueCast_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_Internal_List_getValueCast_x21___redArg___closed__2 = (const lean_object*)&l_Std_Internal_List_getValueCast_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_List_getValueCast_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_List_insertListConst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_List_Prod_toSigma, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Internal_List_insertListConst___redArg___closed__0 = (const lean_object*)&l_Std_Internal_List_insertListConst___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x3f___redArg(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_a_2_);
lean_dec_ref(v_inst_1_);
v___x_4_ = lean_box(0);
return v___x_4_;
}
else
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v_fst_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_head_5_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_head_5_);
v_tail_6_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_tail_6_);
lean_dec_ref(v_x_3_);
v_fst_7_ = lean_ctor_get(v_head_5_, 0);
lean_inc_ref(v_inst_1_);
lean_inc(v_a_2_);
lean_inc(v_fst_7_);
v___x_8_ = lean_apply_2(v_inst_1_, v_fst_7_, v_a_2_);
v___x_9_ = lean_unbox(v___x_8_);
if (v___x_9_ == 0)
{
lean_dec(v_head_5_);
v_x_3_ = v_tail_6_;
goto _start;
}
else
{
lean_object* v___x_11_; 
lean_dec(v_tail_6_);
lean_dec(v_a_2_);
lean_dec_ref(v_inst_1_);
v___x_11_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_11_, 0, v_head_5_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x3f(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_inst_14_, lean_object* v_a_15_, lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_14_, v_a_15_, v_x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntryD___redArg(lean_object* v_inst_18_, lean_object* v_a_19_, lean_object* v_fallback_20_, lean_object* v_x_21_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
lean_dec(v_a_19_);
lean_dec_ref(v_inst_18_);
lean_inc_ref(v_fallback_20_);
return v_fallback_20_;
}
else
{
lean_object* v_head_22_; lean_object* v_tail_23_; lean_object* v_fst_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v_head_22_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_head_22_);
v_tail_23_ = lean_ctor_get(v_x_21_, 1);
lean_inc(v_tail_23_);
lean_dec_ref(v_x_21_);
v_fst_24_ = lean_ctor_get(v_head_22_, 0);
lean_inc_ref(v_inst_18_);
lean_inc(v_a_19_);
lean_inc(v_fst_24_);
v___x_25_ = lean_apply_2(v_inst_18_, v_fst_24_, v_a_19_);
v___x_26_ = lean_unbox(v___x_25_);
if (v___x_26_ == 0)
{
lean_dec(v_head_22_);
v_x_21_ = v_tail_23_;
goto _start;
}
else
{
lean_dec(v_tail_23_);
lean_dec(v_a_19_);
lean_dec_ref(v_inst_18_);
return v_head_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntryD___redArg___boxed(lean_object* v_inst_28_, lean_object* v_a_29_, lean_object* v_fallback_30_, lean_object* v_x_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_Internal_List_getEntryD___redArg(v_inst_28_, v_a_29_, v_fallback_30_, v_x_31_);
lean_dec_ref(v_fallback_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntryD(lean_object* v_00_u03b1_33_, lean_object* v_00_u03b2_34_, lean_object* v_inst_35_, lean_object* v_a_36_, lean_object* v_fallback_37_, lean_object* v_x_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Internal_List_getEntryD___redArg(v_inst_35_, v_a_36_, v_fallback_37_, v_x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntryD___boxed(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_inst_42_, lean_object* v_a_43_, lean_object* v_fallback_44_, lean_object* v_x_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Internal_List_getEntryD(v_00_u03b1_40_, v_00_u03b2_41_, v_inst_42_, v_a_43_, v_fallback_44_, v_x_45_);
lean_dec_ref(v_fallback_44_);
return v_res_46_;
}
}
static lean_object* _init_l_Std_Internal_List_getEntry_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_50_ = ((lean_object*)(l_Std_Internal_List_getEntry_x21___redArg___closed__2));
v___x_51_ = lean_unsigned_to_nat(10u);
v___x_52_ = lean_unsigned_to_nat(67u);
v___x_53_ = ((lean_object*)(l_Std_Internal_List_getEntry_x21___redArg___closed__1));
v___x_54_ = ((lean_object*)(l_Std_Internal_List_getEntry_x21___redArg___closed__0));
v___x_55_ = l_mkPanicMessageWithDecl(v___x_54_, v___x_53_, v___x_52_, v___x_51_, v___x_50_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x21___redArg(lean_object* v_inst_56_, lean_object* v_a_57_, lean_object* v_inst_58_, lean_object* v_x_59_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec(v_a_57_);
lean_dec_ref(v_inst_56_);
v___x_60_ = lean_obj_once(&l_Std_Internal_List_getEntry_x21___redArg___closed__3, &l_Std_Internal_List_getEntry_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getEntry_x21___redArg___closed__3);
v___x_61_ = l_panic___redArg(v_inst_58_, v___x_60_);
return v___x_61_;
}
else
{
lean_object* v_head_62_; lean_object* v_tail_63_; lean_object* v_fst_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v_head_62_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_head_62_);
v_tail_63_ = lean_ctor_get(v_x_59_, 1);
lean_inc(v_tail_63_);
lean_dec_ref(v_x_59_);
v_fst_64_ = lean_ctor_get(v_head_62_, 0);
lean_inc_ref(v_inst_56_);
lean_inc(v_a_57_);
lean_inc(v_fst_64_);
v___x_65_ = lean_apply_2(v_inst_56_, v_fst_64_, v_a_57_);
v___x_66_ = lean_unbox(v___x_65_);
if (v___x_66_ == 0)
{
lean_dec(v_head_62_);
v_x_59_ = v_tail_63_;
goto _start;
}
else
{
lean_dec(v_tail_63_);
lean_dec(v_a_57_);
lean_dec_ref(v_inst_56_);
return v_head_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x21___redArg___boxed(lean_object* v_inst_68_, lean_object* v_a_69_, lean_object* v_inst_70_, lean_object* v_x_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Internal_List_getEntry_x21___redArg(v_inst_68_, v_a_69_, v_inst_70_, v_x_71_);
lean_dec_ref(v_inst_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x21(lean_object* v_00_u03b1_73_, lean_object* v_00_u03b2_74_, lean_object* v_inst_75_, lean_object* v_a_76_, lean_object* v_inst_77_, lean_object* v_x_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Internal_List_getEntry_x21___redArg(v_inst_75_, v_a_76_, v_inst_77_, v_x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x21___boxed(lean_object* v_00_u03b1_80_, lean_object* v_00_u03b2_81_, lean_object* v_inst_82_, lean_object* v_a_83_, lean_object* v_inst_84_, lean_object* v_x_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Internal_List_getEntry_x21(v_00_u03b1_80_, v_00_u03b2_81_, v_inst_82_, v_a_83_, v_inst_84_, v_x_85_);
lean_dec_ref(v_inst_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_87_, lean_object* v_h__1_88_, lean_object* v_h__2_89_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_h__2_89_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_apply_1(v_h__1_88_, v___x_90_);
return v___x_91_;
}
else
{
lean_object* v_head_92_; lean_object* v_tail_93_; lean_object* v_fst_94_; lean_object* v_snd_95_; lean_object* v___x_96_; 
lean_dec(v_h__1_88_);
v_head_92_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_head_92_);
v_tail_93_ = lean_ctor_get(v_x_87_, 1);
lean_inc(v_tail_93_);
lean_dec_ref(v_x_87_);
v_fst_94_ = lean_ctor_get(v_head_92_, 0);
lean_inc(v_fst_94_);
v_snd_95_ = lean_ctor_get(v_head_92_, 1);
lean_inc(v_snd_95_);
lean_dec(v_head_92_);
v___x_96_ = lean_apply_3(v_h__2_89_, v_fst_94_, v_snd_95_, v_tail_93_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_motive_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_h__2_102_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_1(v_h__1_101_, v___x_103_);
return v___x_104_;
}
else
{
lean_object* v_head_105_; lean_object* v_tail_106_; lean_object* v_fst_107_; lean_object* v_snd_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_101_);
v_head_105_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_head_105_);
v_tail_106_ = lean_ctor_get(v_x_100_, 1);
lean_inc(v_tail_106_);
lean_dec_ref(v_x_100_);
v_fst_107_ = lean_ctor_get(v_head_105_, 0);
lean_inc(v_fst_107_);
v_snd_108_ = lean_ctor_get(v_head_105_, 1);
lean_inc(v_snd_108_);
lean_dec(v_head_105_);
v___x_109_ = lean_apply_3(v_h__2_102_, v_fst_107_, v_snd_108_, v_tail_106_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___redArg(lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_h__2_112_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_apply_1(v_h__1_111_, v___x_113_);
return v___x_114_;
}
else
{
lean_object* v_head_115_; lean_object* v_tail_116_; lean_object* v_fst_117_; lean_object* v_snd_118_; lean_object* v___x_119_; 
lean_dec(v_h__1_111_);
v_head_115_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_head_115_);
v_tail_116_ = lean_ctor_get(v_x_110_, 1);
lean_inc(v_tail_116_);
lean_dec_ref(v_x_110_);
v_fst_117_ = lean_ctor_get(v_head_115_, 0);
lean_inc(v_fst_117_);
v_snd_118_ = lean_ctor_get(v_head_115_, 1);
lean_inc(v_snd_118_);
lean_dec(v_head_115_);
v___x_119_ = lean_apply_3(v_h__2_112_, v_fst_117_, v_snd_118_, v_tail_116_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter(lean_object* v_00_u03b1_120_, lean_object* v_00_u03b2_121_, lean_object* v_motive_122_, lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
if (lean_obj_tag(v_x_123_) == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v_h__2_125_);
v___x_126_ = lean_box(0);
v___x_127_ = lean_apply_1(v_h__1_124_, v___x_126_);
return v___x_127_;
}
else
{
lean_object* v_head_128_; lean_object* v_tail_129_; lean_object* v_fst_130_; lean_object* v_snd_131_; lean_object* v___x_132_; 
lean_dec(v_h__1_124_);
v_head_128_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_head_128_);
v_tail_129_ = lean_ctor_get(v_x_123_, 1);
lean_inc(v_tail_129_);
lean_dec_ref(v_x_123_);
v_fst_130_ = lean_ctor_get(v_head_128_, 0);
lean_inc(v_fst_130_);
v_snd_131_ = lean_ctor_get(v_head_128_, 1);
lean_inc(v_snd_131_);
lean_dec(v_head_128_);
v___x_132_ = lean_apply_3(v_h__2_125_, v_fst_130_, v_snd_131_, v_tail_129_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter___redArg(lean_object* v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v_h__2_135_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_apply_1(v_h__1_134_, v___x_136_);
return v___x_137_;
}
else
{
lean_object* v_head_138_; lean_object* v_tail_139_; lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v___x_142_; 
lean_dec(v_h__1_134_);
v_head_138_ = lean_ctor_get(v_x_133_, 0);
lean_inc(v_head_138_);
v_tail_139_ = lean_ctor_get(v_x_133_, 1);
lean_inc(v_tail_139_);
lean_dec_ref(v_x_133_);
v_fst_140_ = lean_ctor_get(v_head_138_, 0);
lean_inc(v_fst_140_);
v_snd_141_ = lean_ctor_get(v_head_138_, 1);
lean_inc(v_snd_141_);
lean_dec(v_head_138_);
v___x_142_ = lean_apply_3(v_h__2_135_, v_fst_140_, v_snd_141_, v_tail_139_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter(lean_object* v_00_u03b1_143_, lean_object* v_00_u03b2_144_, lean_object* v_motive_145_, lean_object* v_x_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_h__2_148_);
v___x_149_ = lean_box(0);
v___x_150_ = lean_apply_1(v_h__1_147_, v___x_149_);
return v___x_150_;
}
else
{
lean_object* v_head_151_; lean_object* v_tail_152_; lean_object* v_fst_153_; lean_object* v_snd_154_; lean_object* v___x_155_; 
lean_dec(v_h__1_147_);
v_head_151_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_head_151_);
v_tail_152_ = lean_ctor_get(v_x_146_, 1);
lean_inc(v_tail_152_);
lean_dec_ref(v_x_146_);
v_fst_153_ = lean_ctor_get(v_head_151_, 0);
lean_inc(v_fst_153_);
v_snd_154_ = lean_ctor_get(v_head_151_, 1);
lean_inc(v_snd_154_);
lean_dec(v_head_151_);
v___x_155_ = lean_apply_3(v_h__2_148_, v_fst_153_, v_snd_154_, v_tail_152_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f___redArg(lean_object* v_inst_156_, lean_object* v_a_157_, lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v___x_159_; 
lean_dec(v_a_157_);
lean_dec_ref(v_inst_156_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v_head_160_; lean_object* v_tail_161_; lean_object* v_fst_162_; lean_object* v_snd_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v_head_160_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_head_160_);
v_tail_161_ = lean_ctor_get(v_x_158_, 1);
lean_inc(v_tail_161_);
lean_dec_ref(v_x_158_);
v_fst_162_ = lean_ctor_get(v_head_160_, 0);
lean_inc(v_fst_162_);
v_snd_163_ = lean_ctor_get(v_head_160_, 1);
lean_inc(v_snd_163_);
lean_dec(v_head_160_);
lean_inc_ref(v_inst_156_);
lean_inc(v_a_157_);
v___x_164_ = lean_apply_2(v_inst_156_, v_fst_162_, v_a_157_);
v___x_165_ = lean_unbox(v___x_164_);
if (v___x_165_ == 0)
{
lean_dec(v_snd_163_);
v_x_158_ = v_tail_161_;
goto _start;
}
else
{
lean_object* v___x_167_; 
lean_dec(v_tail_161_);
lean_dec(v_a_157_);
lean_dec_ref(v_inst_156_);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v_snd_163_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f(lean_object* v_00_u03b1_168_, lean_object* v_00_u03b2_169_, lean_object* v_inst_170_, lean_object* v_a_171_, lean_object* v_x_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_170_, v_a_171_, v_x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___redArg(lean_object* v_x_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_h__2_176_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_apply_1(v_h__1_175_, v___x_177_);
return v___x_178_;
}
else
{
lean_object* v_head_179_; lean_object* v_tail_180_; lean_object* v_fst_181_; lean_object* v_snd_182_; lean_object* v___x_183_; 
lean_dec(v_h__1_175_);
v_head_179_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_head_179_);
v_tail_180_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_tail_180_);
lean_dec_ref(v_x_174_);
v_fst_181_ = lean_ctor_get(v_head_179_, 0);
lean_inc(v_fst_181_);
v_snd_182_ = lean_ctor_get(v_head_179_, 1);
lean_inc(v_snd_182_);
lean_dec(v_head_179_);
v___x_183_ = lean_apply_3(v_h__2_176_, v_fst_181_, v_snd_182_, v_tail_180_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_motive_186_, lean_object* v_x_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v_h__2_189_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_apply_1(v_h__1_188_, v___x_190_);
return v___x_191_;
}
else
{
lean_object* v_head_192_; lean_object* v_tail_193_; lean_object* v_fst_194_; lean_object* v_snd_195_; lean_object* v___x_196_; 
lean_dec(v_h__1_188_);
v_head_192_ = lean_ctor_get(v_x_187_, 0);
lean_inc(v_head_192_);
v_tail_193_ = lean_ctor_get(v_x_187_, 1);
lean_inc(v_tail_193_);
lean_dec_ref(v_x_187_);
v_fst_194_ = lean_ctor_get(v_head_192_, 0);
lean_inc(v_fst_194_);
v_snd_195_ = lean_ctor_get(v_head_192_, 1);
lean_inc(v_snd_195_);
lean_dec(v_head_192_);
v___x_196_ = lean_apply_3(v_h__2_189_, v_fst_194_, v_snd_195_, v_tail_193_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f___redArg(lean_object* v_inst_197_, lean_object* v_a_198_, lean_object* v_x_199_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v___x_200_; 
lean_dec(v_a_198_);
lean_dec_ref(v_inst_197_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v_head_201_; lean_object* v_tail_202_; lean_object* v_fst_203_; lean_object* v_snd_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v_head_201_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_head_201_);
v_tail_202_ = lean_ctor_get(v_x_199_, 1);
lean_inc(v_tail_202_);
lean_dec_ref(v_x_199_);
v_fst_203_ = lean_ctor_get(v_head_201_, 0);
lean_inc(v_fst_203_);
v_snd_204_ = lean_ctor_get(v_head_201_, 1);
lean_inc(v_snd_204_);
lean_dec(v_head_201_);
lean_inc_ref(v_inst_197_);
lean_inc(v_a_198_);
v___x_205_ = lean_apply_2(v_inst_197_, v_fst_203_, v_a_198_);
v___x_206_ = lean_unbox(v___x_205_);
if (v___x_206_ == 0)
{
lean_dec(v_snd_204_);
v_x_199_ = v_tail_202_;
goto _start;
}
else
{
lean_object* v___x_208_; 
lean_dec(v_tail_202_);
lean_dec(v_a_198_);
lean_dec_ref(v_inst_197_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v_snd_204_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_a_213_, lean_object* v_x_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_211_, v_a_213_, v_x_214_);
return v___x_215_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg___lam__0(lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_l_u2082_218_, lean_object* v_x_219_){
_start:
{
lean_object* v_fst_220_; lean_object* v_snd_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_fst_220_ = lean_ctor_get(v_x_219_, 0);
lean_inc_n(v_fst_220_, 2);
v_snd_221_ = lean_ctor_get(v_x_219_, 1);
lean_inc(v_snd_221_);
lean_dec_ref(v_x_219_);
v___x_222_ = lean_apply_1(v_inst_216_, v_fst_220_);
v___x_223_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_217_, v_fst_220_, v_l_u2082_218_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v_snd_221_);
v___x_225_ = l_Option_instBEq_beq___redArg(v___x_222_, v___x_223_, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___lam__0___boxed(lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_l_u2082_228_, lean_object* v_x_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Std_Internal_List_beqModel___redArg___lam__0(v_inst_226_, v_inst_227_, v_l_u2082_228_, v_x_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg(lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_l_u2081_234_, lean_object* v_l_u2082_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = l_List_lengthTR___redArg(v_l_u2081_234_);
v___x_237_ = l_List_lengthTR___redArg(v_l_u2082_235_);
v___x_238_ = lean_nat_dec_eq(v___x_236_, v___x_237_);
lean_dec(v___x_237_);
lean_dec(v___x_236_);
if (v___x_238_ == 0)
{
lean_dec(v_l_u2082_235_);
lean_dec(v_l_u2081_234_);
lean_dec_ref(v_inst_233_);
lean_dec_ref(v_inst_232_);
return v___x_238_;
}
else
{
lean_object* v___f_239_; uint8_t v___x_240_; 
v___f_239_ = lean_alloc_closure((void*)(l_Std_Internal_List_beqModel___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_239_, 0, v_inst_233_);
lean_closure_set(v___f_239_, 1, v_inst_232_);
lean_closure_set(v___f_239_, 2, v_l_u2082_235_);
v___x_240_ = l_List_all___redArg(v_l_u2081_234_, v___f_239_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___boxed(lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_l_u2081_243_, lean_object* v_l_u2082_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Std_Internal_List_beqModel___redArg(v_inst_241_, v_inst_242_, v_l_u2081_243_, v_l_u2082_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_l_u2081_252_, lean_object* v_l_u2082_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = l_Std_Internal_List_beqModel___redArg(v_inst_249_, v_inst_251_, v_l_u2081_252_, v_l_u2082_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___boxed(lean_object* v_00_u03b1_255_, lean_object* v_00_u03b2_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_l_u2081_260_, lean_object* v_l_u2082_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Std_Internal_List_beqModel(v_00_u03b1_255_, v_00_u03b2_256_, v_inst_257_, v_inst_258_, v_inst_259_, v_l_u2081_260_, v_l_u2082_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter___redArg(lean_object* v_x_264_, lean_object* v_h__1_265_, lean_object* v_h__2_266_){
_start:
{
if (lean_obj_tag(v_x_264_) == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_h__2_266_);
v___x_267_ = lean_box(0);
v___x_268_ = lean_apply_1(v_h__1_265_, v___x_267_);
return v___x_268_;
}
else
{
lean_object* v_head_269_; lean_object* v_tail_270_; lean_object* v_fst_271_; lean_object* v_snd_272_; lean_object* v___x_273_; 
lean_dec(v_h__1_265_);
v_head_269_ = lean_ctor_get(v_x_264_, 0);
lean_inc(v_head_269_);
v_tail_270_ = lean_ctor_get(v_x_264_, 1);
lean_inc(v_tail_270_);
lean_dec_ref(v_x_264_);
v_fst_271_ = lean_ctor_get(v_head_269_, 0);
lean_inc(v_fst_271_);
v_snd_272_ = lean_ctor_get(v_head_269_, 1);
lean_inc(v_snd_272_);
lean_dec(v_head_269_);
v___x_273_ = lean_apply_3(v_h__2_266_, v_fst_271_, v_snd_272_, v_tail_270_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_motive_276_, lean_object* v_x_277_, lean_object* v_h__1_278_, lean_object* v_h__2_279_){
_start:
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v_h__2_279_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_apply_1(v_h__1_278_, v___x_280_);
return v___x_281_;
}
else
{
lean_object* v_head_282_; lean_object* v_tail_283_; lean_object* v_fst_284_; lean_object* v_snd_285_; lean_object* v___x_286_; 
lean_dec(v_h__1_278_);
v_head_282_ = lean_ctor_get(v_x_277_, 0);
lean_inc(v_head_282_);
v_tail_283_ = lean_ctor_get(v_x_277_, 1);
lean_inc(v_tail_283_);
lean_dec_ref(v_x_277_);
v_fst_284_ = lean_ctor_get(v_head_282_, 0);
lean_inc(v_fst_284_);
v_snd_285_ = lean_ctor_get(v_head_282_, 1);
lean_inc(v_snd_285_);
lean_dec(v_head_282_);
v___x_286_ = lean_apply_3(v_h__2_279_, v_fst_284_, v_snd_285_, v_tail_283_);
return v___x_286_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg___lam__0(lean_object* v_inst_287_, lean_object* v_l_u2082_288_, lean_object* v_inst_289_, lean_object* v_x_290_){
_start:
{
lean_object* v_fst_291_; lean_object* v_snd_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_fst_291_ = lean_ctor_get(v_x_290_, 0);
lean_inc(v_fst_291_);
v_snd_292_ = lean_ctor_get(v_x_290_, 1);
lean_inc(v_snd_292_);
lean_dec_ref(v_x_290_);
v___x_293_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_287_, v_fst_291_, v_l_u2082_288_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v_snd_292_);
v___x_295_ = l_Option_instBEq_beq___redArg(v_inst_289_, v___x_293_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed(lean_object* v_inst_296_, lean_object* v_l_u2082_297_, lean_object* v_inst_298_, lean_object* v_x_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_Internal_List_Const_beqModel___redArg___lam__0(v_inst_296_, v_l_u2082_297_, v_inst_298_, v_x_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg(lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_l_u2081_304_, lean_object* v_l_u2082_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = l_List_lengthTR___redArg(v_l_u2081_304_);
v___x_307_ = l_List_lengthTR___redArg(v_l_u2082_305_);
v___x_308_ = lean_nat_dec_eq(v___x_306_, v___x_307_);
lean_dec(v___x_307_);
lean_dec(v___x_306_);
if (v___x_308_ == 0)
{
lean_dec(v_l_u2082_305_);
lean_dec(v_l_u2081_304_);
lean_dec_ref(v_inst_303_);
lean_dec_ref(v_inst_302_);
return v___x_308_;
}
else
{
lean_object* v___f_309_; uint8_t v___x_310_; 
v___f_309_ = lean_alloc_closure((void*)(l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_309_, 0, v_inst_302_);
lean_closure_set(v___f_309_, 1, v_l_u2082_305_);
lean_closure_set(v___f_309_, 2, v_inst_303_);
v___x_310_ = l_List_all___redArg(v_l_u2081_304_, v___f_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___boxed(lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_l_u2081_313_, lean_object* v_l_u2082_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_311_, v_inst_312_, v_l_u2081_313_, v_l_u2082_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel(lean_object* v_00_u03b1_317_, lean_object* v_00_u03b2_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_l_u2081_321_, lean_object* v_l_u2082_322_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_319_, v_inst_320_, v_l_u2081_321_, v_l_u2082_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___boxed(lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_l_u2081_328_, lean_object* v_l_u2082_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Std_Internal_List_Const_beqModel(v_00_u03b1_324_, v_00_u03b2_325_, v_inst_326_, v_inst_327_, v_l_u2081_328_, v_l_u2082_329_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_332_) == 0)
{
lean_object* v___x_334_; 
lean_dec(v_x_333_);
v___x_334_ = lean_box(0);
return v___x_334_;
}
else
{
lean_object* v_val_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
v_val_335_ = lean_ctor_get(v_x_332_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_x_332_);
if (v_isSharedCheck_343_ == 0)
{
v___x_337_ = v_x_332_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_val_335_);
lean_dec(v_x_332_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_apply_2(v_x_333_, v_val_335_, lean_box(0));
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_339_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(v_x_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___redArg(lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_h__1_351_, lean_object* v_h__2_352_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_object* v___x_353_; 
lean_dec(v_h__2_352_);
v___x_353_ = lean_apply_1(v_h__1_351_, v_x_350_);
return v___x_353_;
}
else
{
lean_object* v_val_354_; lean_object* v___x_355_; 
lean_dec(v_h__1_351_);
v_val_354_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_val_354_);
lean_dec_ref(v_x_349_);
v___x_355_ = lean_apply_2(v_h__2_352_, v_val_354_, v_x_350_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_motive_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_h__1_361_, lean_object* v_h__2_362_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
lean_object* v___x_363_; 
lean_dec(v_h__2_362_);
v___x_363_ = lean_apply_1(v_h__1_361_, v_x_360_);
return v___x_363_;
}
else
{
lean_object* v_val_364_; lean_object* v___x_365_; 
lean_dec(v_h__1_361_);
v_val_364_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_val_364_);
lean_dec_ref(v_x_359_);
v___x_365_ = lean_apply_2(v_h__2_362_, v_val_364_, v_x_360_);
return v___x_365_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey___redArg(lean_object* v_inst_366_, lean_object* v_a_367_, lean_object* v_x_368_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
uint8_t v___x_369_; 
lean_dec(v_a_367_);
lean_dec_ref(v_inst_366_);
v___x_369_ = 0;
return v___x_369_;
}
else
{
lean_object* v_head_370_; lean_object* v_tail_371_; lean_object* v_fst_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_head_370_ = lean_ctor_get(v_x_368_, 0);
lean_inc(v_head_370_);
v_tail_371_ = lean_ctor_get(v_x_368_, 1);
lean_inc(v_tail_371_);
lean_dec_ref(v_x_368_);
v_fst_372_ = lean_ctor_get(v_head_370_, 0);
lean_inc(v_fst_372_);
lean_dec(v_head_370_);
lean_inc_ref(v_inst_366_);
lean_inc(v_a_367_);
v___x_373_ = lean_apply_2(v_inst_366_, v_fst_372_, v_a_367_);
v___x_374_ = lean_unbox(v___x_373_);
if (v___x_374_ == 0)
{
v_x_368_ = v_tail_371_;
goto _start;
}
else
{
uint8_t v___x_376_; 
lean_dec(v_tail_371_);
lean_dec(v_a_367_);
lean_dec_ref(v_inst_366_);
v___x_376_ = lean_unbox(v___x_373_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___redArg___boxed(lean_object* v_inst_377_, lean_object* v_a_378_, lean_object* v_x_379_){
_start:
{
uint8_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l_Std_Internal_List_containsKey___redArg(v_inst_377_, v_a_378_, v_x_379_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey(lean_object* v_00_u03b1_382_, lean_object* v_00_u03b2_383_, lean_object* v_inst_384_, lean_object* v_a_385_, lean_object* v_x_386_){
_start:
{
uint8_t v___x_387_; 
v___x_387_ = l_Std_Internal_List_containsKey___redArg(v_inst_384_, v_a_385_, v_x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___boxed(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_inst_390_, lean_object* v_a_391_, lean_object* v_x_392_){
_start:
{
uint8_t v_res_393_; lean_object* v_r_394_; 
v_res_393_ = l_Std_Internal_List_containsKey(v_00_u03b1_388_, v_00_u03b2_389_, v_inst_390_, v_a_391_, v_x_392_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry___redArg(lean_object* v_inst_395_, lean_object* v_a_396_, lean_object* v_l_397_){
_start:
{
lean_object* v___x_398_; lean_object* v_val_399_; 
v___x_398_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_395_, v_a_396_, v_l_397_);
v_val_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_val_399_);
lean_dec(v___x_398_);
return v_val_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry(lean_object* v_00_u03b1_400_, lean_object* v_00_u03b2_401_, lean_object* v_inst_402_, lean_object* v_a_403_, lean_object* v_l_404_, lean_object* v_h_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_Internal_List_getEntry___redArg(v_inst_402_, v_a_403_, v_l_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue___redArg(lean_object* v_inst_407_, lean_object* v_a_408_, lean_object* v_l_409_){
_start:
{
lean_object* v___x_410_; lean_object* v_val_411_; 
v___x_410_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_407_, v_a_408_, v_l_409_);
v_val_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_val_411_);
lean_dec(v___x_410_);
return v_val_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_inst_414_, lean_object* v_a_415_, lean_object* v_l_416_, lean_object* v_h_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Std_Internal_List_getValue___redArg(v_inst_414_, v_a_415_, v_l_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast___redArg(lean_object* v_inst_419_, lean_object* v_a_420_, lean_object* v_l_421_){
_start:
{
lean_object* v___x_422_; lean_object* v_val_423_; 
v___x_422_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_419_, v_a_420_, v_l_421_);
v_val_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_val_423_);
lean_dec(v___x_422_);
return v_val_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast(lean_object* v_00_u03b1_424_, lean_object* v_00_u03b2_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_a_428_, lean_object* v_l_429_, lean_object* v_h_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_Internal_List_getValueCast___redArg(v_inst_426_, v_a_428_, v_l_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg(lean_object* v_inst_432_, lean_object* v_a_433_, lean_object* v_l_434_, lean_object* v_fallback_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_432_, v_a_433_, v_l_434_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_inc(v_fallback_435_);
return v_fallback_435_;
}
else
{
lean_object* v_val_437_; 
v_val_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_437_);
lean_dec_ref(v___x_436_);
return v_val_437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg___boxed(lean_object* v_inst_438_, lean_object* v_a_439_, lean_object* v_l_440_, lean_object* v_fallback_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_Internal_List_getValueCastD___redArg(v_inst_438_, v_a_439_, v_l_440_, v_fallback_441_);
lean_dec(v_fallback_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD(lean_object* v_00_u03b1_443_, lean_object* v_00_u03b2_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_a_447_, lean_object* v_l_448_, lean_object* v_fallback_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_Internal_List_getValueCastD___redArg(v_inst_445_, v_a_447_, v_l_448_, v_fallback_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___boxed(lean_object* v_00_u03b1_451_, lean_object* v_00_u03b2_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_a_455_, lean_object* v_l_456_, lean_object* v_fallback_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_Internal_List_getValueCastD(v_00_u03b1_451_, v_00_u03b2_452_, v_inst_453_, v_inst_454_, v_a_455_, v_l_456_, v_fallback_457_);
lean_dec(v_fallback_457_);
return v_res_458_;
}
}
static lean_object* _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_462_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__2));
v___x_463_ = lean_unsigned_to_nat(14u);
v___x_464_ = lean_unsigned_to_nat(22u);
v___x_465_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__1));
v___x_466_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__0));
v___x_467_ = l_mkPanicMessageWithDecl(v___x_466_, v___x_465_, v___x_464_, v___x_463_, v___x_462_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___redArg(lean_object* v_inst_468_, lean_object* v_a_469_, lean_object* v_inst_470_, lean_object* v_l_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_468_, v_a_469_, v_l_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_474_ = l_panic___redArg(v_inst_470_, v___x_473_);
return v___x_474_;
}
else
{
lean_object* v_val_475_; 
v_val_475_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_val_475_);
lean_dec_ref(v___x_472_);
return v_val_475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___redArg___boxed(lean_object* v_inst_476_, lean_object* v_a_477_, lean_object* v_inst_478_, lean_object* v_l_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_Internal_List_getValueCast_x21___redArg(v_inst_476_, v_a_477_, v_inst_478_, v_l_479_);
lean_dec(v_inst_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21(lean_object* v_00_u03b1_481_, lean_object* v_00_u03b2_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_a_485_, lean_object* v_inst_486_, lean_object* v_l_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_Internal_List_getValueCast_x21___redArg(v_inst_483_, v_a_485_, v_inst_486_, v_l_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___boxed(lean_object* v_00_u03b1_489_, lean_object* v_00_u03b2_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_a_493_, lean_object* v_inst_494_, lean_object* v_l_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_Internal_List_getValueCast_x21(v_00_u03b1_489_, v_00_u03b2_490_, v_inst_491_, v_inst_492_, v_a_493_, v_inst_494_, v_l_495_);
lean_dec(v_inst_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg(lean_object* v_inst_497_, lean_object* v_a_498_, lean_object* v_l_499_, lean_object* v_fallback_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_497_, v_a_498_, v_l_499_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_inc(v_fallback_500_);
return v_fallback_500_;
}
else
{
lean_object* v_val_502_; 
v_val_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_val_502_);
lean_dec_ref(v___x_501_);
return v_val_502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg___boxed(lean_object* v_inst_503_, lean_object* v_a_504_, lean_object* v_l_505_, lean_object* v_fallback_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_Internal_List_getValueD___redArg(v_inst_503_, v_a_504_, v_l_505_, v_fallback_506_);
lean_dec(v_fallback_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_inst_510_, lean_object* v_a_511_, lean_object* v_l_512_, lean_object* v_fallback_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_Internal_List_getValueD___redArg(v_inst_510_, v_a_511_, v_l_512_, v_fallback_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___boxed(lean_object* v_00_u03b1_515_, lean_object* v_00_u03b2_516_, lean_object* v_inst_517_, lean_object* v_a_518_, lean_object* v_l_519_, lean_object* v_fallback_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_Internal_List_getValueD(v_00_u03b1_515_, v_00_u03b2_516_, v_inst_517_, v_a_518_, v_l_519_, v_fallback_520_);
lean_dec(v_fallback_520_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg(lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_a_524_, lean_object* v_l_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_522_, v_a_524_, v_l_525_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_528_ = l_panic___redArg(v_inst_523_, v___x_527_);
return v___x_528_;
}
else
{
lean_object* v_val_529_; 
v_val_529_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_val_529_);
lean_dec_ref(v___x_526_);
return v_val_529_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg___boxed(lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_a_532_, lean_object* v_l_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Internal_List_getValue_x21___redArg(v_inst_530_, v_inst_531_, v_a_532_, v_l_533_);
lean_dec(v_inst_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21(lean_object* v_00_u03b1_535_, lean_object* v_00_u03b2_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_a_539_, lean_object* v_l_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_Internal_List_getValue_x21___redArg(v_inst_537_, v_inst_538_, v_a_539_, v_l_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___boxed(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_a_546_, lean_object* v_l_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Internal_List_getValue_x21(v_00_u03b1_542_, v_00_u03b2_543_, v_inst_544_, v_inst_545_, v_a_546_, v_l_547_);
lean_dec(v_inst_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f___redArg(lean_object* v_inst_549_, lean_object* v_a_550_, lean_object* v_x_551_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v___x_552_; 
lean_dec(v_a_550_);
lean_dec_ref(v_inst_549_);
v___x_552_ = lean_box(0);
return v___x_552_;
}
else
{
lean_object* v_head_553_; lean_object* v_tail_554_; lean_object* v_fst_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_head_553_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_head_553_);
v_tail_554_ = lean_ctor_get(v_x_551_, 1);
lean_inc(v_tail_554_);
lean_dec_ref(v_x_551_);
v_fst_555_ = lean_ctor_get(v_head_553_, 0);
lean_inc_n(v_fst_555_, 2);
lean_dec(v_head_553_);
lean_inc_ref(v_inst_549_);
lean_inc(v_a_550_);
v___x_556_ = lean_apply_2(v_inst_549_, v_fst_555_, v_a_550_);
v___x_557_ = lean_unbox(v___x_556_);
if (v___x_557_ == 0)
{
lean_dec(v_fst_555_);
v_x_551_ = v_tail_554_;
goto _start;
}
else
{
lean_object* v___x_559_; 
lean_dec(v_tail_554_);
lean_dec(v_a_550_);
lean_dec_ref(v_inst_549_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_fst_555_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f(lean_object* v_00_u03b1_560_, lean_object* v_00_u03b2_561_, lean_object* v_inst_562_, lean_object* v_a_563_, lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_562_, v_a_563_, v_x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey___redArg(lean_object* v_inst_566_, lean_object* v_a_567_, lean_object* v_l_568_){
_start:
{
lean_object* v___x_569_; lean_object* v_val_570_; 
v___x_569_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_566_, v_a_567_, v_l_568_);
v_val_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_val_570_);
lean_dec(v___x_569_);
return v_val_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_inst_573_, lean_object* v_a_574_, lean_object* v_l_575_, lean_object* v_h_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_Internal_List_getKey___redArg(v_inst_573_, v_a_574_, v_l_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg(lean_object* v_inst_578_, lean_object* v_a_579_, lean_object* v_l_580_, lean_object* v_fallback_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_578_, v_a_579_, v_l_580_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_inc(v_fallback_581_);
return v_fallback_581_;
}
else
{
lean_object* v_val_583_; 
v_val_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_val_583_);
lean_dec_ref(v___x_582_);
return v_val_583_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg___boxed(lean_object* v_inst_584_, lean_object* v_a_585_, lean_object* v_l_586_, lean_object* v_fallback_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_Internal_List_getKeyD___redArg(v_inst_584_, v_a_585_, v_l_586_, v_fallback_587_);
lean_dec(v_fallback_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD(lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_, lean_object* v_inst_591_, lean_object* v_a_592_, lean_object* v_l_593_, lean_object* v_fallback_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Std_Internal_List_getKeyD___redArg(v_inst_591_, v_a_592_, v_l_593_, v_fallback_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___boxed(lean_object* v_00_u03b1_596_, lean_object* v_00_u03b2_597_, lean_object* v_inst_598_, lean_object* v_a_599_, lean_object* v_l_600_, lean_object* v_fallback_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_Internal_List_getKeyD(v_00_u03b1_596_, v_00_u03b2_597_, v_inst_598_, v_a_599_, v_l_600_, v_fallback_601_);
lean_dec(v_fallback_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg(lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_a_605_, lean_object* v_l_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_603_, v_a_605_, v_l_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_609_ = l_panic___redArg(v_inst_604_, v___x_608_);
return v___x_609_;
}
else
{
lean_object* v_val_610_; 
v_val_610_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_val_610_);
lean_dec_ref(v___x_607_);
return v_val_610_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg___boxed(lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_a_613_, lean_object* v_l_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Std_Internal_List_getKey_x21___redArg(v_inst_611_, v_inst_612_, v_a_613_, v_l_614_);
lean_dec(v_inst_612_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21(lean_object* v_00_u03b1_616_, lean_object* v_00_u03b2_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_a_620_, lean_object* v_l_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_Internal_List_getKey_x21___redArg(v_inst_618_, v_inst_619_, v_a_620_, v_l_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___boxed(lean_object* v_00_u03b1_623_, lean_object* v_00_u03b2_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_a_627_, lean_object* v_l_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_Internal_List_getKey_x21(v_00_u03b1_623_, v_00_u03b2_624_, v_inst_625_, v_inst_626_, v_a_627_, v_l_628_);
lean_dec(v_inst_626_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry___redArg(lean_object* v_inst_630_, lean_object* v_k_631_, lean_object* v_v_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
lean_object* v___x_634_; 
lean_dec(v_v_632_);
lean_dec(v_k_631_);
lean_dec_ref(v_inst_630_);
v___x_634_ = lean_box(0);
return v___x_634_;
}
else
{
lean_object* v_head_635_; lean_object* v_tail_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_659_; 
v_head_635_ = lean_ctor_get(v_x_633_, 0);
v_tail_636_ = lean_ctor_get(v_x_633_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_659_ == 0)
{
v___x_638_ = v_x_633_;
v_isShared_639_ = v_isSharedCheck_659_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_tail_636_);
lean_inc(v_head_635_);
lean_dec(v_x_633_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_659_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_fst_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_fst_640_ = lean_ctor_get(v_head_635_, 0);
lean_inc_ref(v_inst_630_);
lean_inc(v_k_631_);
lean_inc(v_fst_640_);
v___x_641_ = lean_apply_2(v_inst_630_, v_fst_640_, v_k_631_);
v___x_642_ = lean_unbox(v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_630_, v_k_631_, v_v_632_, v_tail_636_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v___x_643_);
v___x_645_ = v___x_638_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_head_635_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v_inst_630_);
v_isSharedCheck_656_ = !lean_is_exclusive(v_head_635_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; lean_object* v_unused_658_; 
v_unused_657_ = lean_ctor_get(v_head_635_, 1);
lean_dec(v_unused_657_);
v_unused_658_ = lean_ctor_get(v_head_635_, 0);
lean_dec(v_unused_658_);
v___x_648_ = v_head_635_;
v_isShared_649_ = v_isSharedCheck_656_;
goto v_resetjp_647_;
}
else
{
lean_dec(v_head_635_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_656_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_v_632_);
lean_ctor_set(v___x_648_, 0, v_k_631_);
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_v_632_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_651_);
v___x_653_ = v___x_638_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_tail_636_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry(lean_object* v_00_u03b1_660_, lean_object* v_00_u03b2_661_, lean_object* v_inst_662_, lean_object* v_k_663_, lean_object* v_v_664_, lean_object* v_x_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_662_, v_k_663_, v_v_664_, v_x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey___redArg(lean_object* v_inst_667_, lean_object* v_k_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
lean_object* v___x_670_; 
lean_dec(v_k_668_);
lean_dec_ref(v_inst_667_);
v___x_670_ = lean_box(0);
return v___x_670_;
}
else
{
lean_object* v_head_671_; lean_object* v_tail_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_683_; 
v_head_671_ = lean_ctor_get(v_x_669_, 0);
v_tail_672_ = lean_ctor_get(v_x_669_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_669_);
if (v_isSharedCheck_683_ == 0)
{
v___x_674_ = v_x_669_;
v_isShared_675_ = v_isSharedCheck_683_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_tail_672_);
lean_inc(v_head_671_);
lean_dec(v_x_669_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_683_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_fst_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_fst_676_ = lean_ctor_get(v_head_671_, 0);
lean_inc_ref(v_inst_667_);
lean_inc(v_k_668_);
lean_inc(v_fst_676_);
v___x_677_ = lean_apply_2(v_inst_667_, v_fst_676_, v_k_668_);
v___x_678_ = lean_unbox(v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = l_Std_Internal_List_eraseKey___redArg(v_inst_667_, v_k_668_, v_tail_672_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_679_);
v___x_681_ = v___x_674_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_head_671_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
else
{
lean_del_object(v___x_674_);
lean_dec(v_head_671_);
lean_dec(v_k_668_);
lean_dec_ref(v_inst_667_);
return v_tail_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey(lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_inst_686_, lean_object* v_k_687_, lean_object* v_x_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Std_Internal_List_eraseKey___redArg(v_inst_686_, v_k_687_, v_x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry___redArg(lean_object* v_inst_690_, lean_object* v_k_691_, lean_object* v_v_692_, lean_object* v_l_693_){
_start:
{
uint8_t v___x_694_; 
lean_inc(v_l_693_);
lean_inc(v_k_691_);
lean_inc_ref(v_inst_690_);
v___x_694_ = l_Std_Internal_List_containsKey___redArg(v_inst_690_, v_k_691_, v_l_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec_ref(v_inst_690_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_k_691_);
lean_ctor_set(v___x_695_, 1, v_v_692_);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v_l_693_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_690_, v_k_691_, v_v_692_, v_l_693_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_inst_700_, lean_object* v_k_701_, lean_object* v_v_702_, lean_object* v_l_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_Internal_List_insertEntry___redArg(v_inst_700_, v_k_701_, v_v_702_, v_l_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew___redArg(lean_object* v_inst_705_, lean_object* v_k_706_, lean_object* v_v_707_, lean_object* v_l_708_){
_start:
{
uint8_t v___x_709_; 
lean_inc(v_l_708_);
lean_inc(v_k_706_);
v___x_709_ = l_Std_Internal_List_containsKey___redArg(v_inst_705_, v_k_706_, v_l_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_k_706_);
lean_ctor_set(v___x_710_, 1, v_v_707_);
v___x_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_l_708_);
return v___x_711_;
}
else
{
lean_dec(v_v_707_);
lean_dec(v_k_706_);
return v_l_708_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew(lean_object* v_00_u03b1_712_, lean_object* v_00_u03b2_713_, lean_object* v_inst_714_, lean_object* v_k_715_, lean_object* v_v_716_, lean_object* v_l_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_714_, v_k_715_, v_v_716_, v_l_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_719_, lean_object* v_h__1_720_, lean_object* v_h__2_721_){
_start:
{
if (lean_obj_tag(v_x_719_) == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec(v_h__2_721_);
v___x_722_ = lean_box(0);
v___x_723_ = lean_apply_1(v_h__1_720_, v___x_722_);
return v___x_723_;
}
else
{
lean_object* v_val_724_; lean_object* v___x_725_; 
lean_dec(v_h__1_720_);
v_val_724_ = lean_ctor_get(v_x_719_, 0);
lean_inc(v_val_724_);
lean_dec_ref(v_x_719_);
v___x_725_ = lean_apply_1(v_h__2_721_, v_val_724_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_726_, lean_object* v_motive_727_, lean_object* v_x_728_, lean_object* v_h__1_729_, lean_object* v_h__2_730_){
_start:
{
if (lean_obj_tag(v_x_728_) == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec(v_h__2_730_);
v___x_731_ = lean_box(0);
v___x_732_ = lean_apply_1(v_h__1_729_, v___x_731_);
return v___x_732_;
}
else
{
lean_object* v_val_733_; lean_object* v___x_734_; 
lean_dec(v_h__1_729_);
v_val_733_ = lean_ctor_get(v_x_728_, 0);
lean_inc(v_val_733_);
lean_dec_ref(v_x_728_);
v___x_734_ = lean_apply_1(v_h__2_730_, v_val_733_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_735_, lean_object* v_h__1_736_, lean_object* v_h__2_737_){
_start:
{
if (lean_obj_tag(v_x_735_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_739_; 
lean_dec(v_h__2_737_);
v_a_738_ = lean_ctor_get(v_x_735_, 0);
lean_inc(v_a_738_);
lean_dec_ref(v_x_735_);
v___x_739_ = lean_apply_1(v_h__1_736_, v_a_738_);
return v___x_739_;
}
else
{
lean_object* v_a_740_; lean_object* v___x_741_; 
lean_dec(v_h__1_736_);
v_a_740_ = lean_ctor_get(v_x_735_, 0);
lean_inc(v_a_740_);
lean_dec_ref(v_x_735_);
v___x_741_ = lean_apply_1(v_h__2_737_, v_a_740_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_742_, lean_object* v_motive_743_, lean_object* v_x_744_, lean_object* v_h__1_745_, lean_object* v_h__2_746_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
lean_dec(v_h__2_746_);
v_a_747_ = lean_ctor_get(v_x_744_, 0);
lean_inc(v_a_747_);
lean_dec_ref(v_x_744_);
v___x_748_ = lean_apply_1(v_h__1_745_, v_a_747_);
return v___x_748_;
}
else
{
lean_object* v_a_749_; lean_object* v___x_750_; 
lean_dec(v_h__1_745_);
v_a_749_ = lean_ctor_get(v_x_744_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v_x_744_);
v___x_750_ = lean_apply_1(v_h__2_746_, v_a_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList___redArg(lean_object* v_inst_751_, lean_object* v_l_752_, lean_object* v_toInsert_753_){
_start:
{
if (lean_obj_tag(v_toInsert_753_) == 0)
{
lean_dec_ref(v_inst_751_);
return v_l_752_;
}
else
{
lean_object* v_head_754_; lean_object* v_tail_755_; lean_object* v_fst_756_; lean_object* v_snd_757_; lean_object* v___x_758_; 
v_head_754_ = lean_ctor_get(v_toInsert_753_, 0);
lean_inc(v_head_754_);
v_tail_755_ = lean_ctor_get(v_toInsert_753_, 1);
lean_inc(v_tail_755_);
lean_dec_ref(v_toInsert_753_);
v_fst_756_ = lean_ctor_get(v_head_754_, 0);
lean_inc(v_fst_756_);
v_snd_757_ = lean_ctor_get(v_head_754_, 1);
lean_inc(v_snd_757_);
lean_dec(v_head_754_);
lean_inc_ref(v_inst_751_);
v___x_758_ = l_Std_Internal_List_insertEntry___redArg(v_inst_751_, v_fst_756_, v_snd_757_, v_l_752_);
v_l_752_ = v___x_758_;
v_toInsert_753_ = v_tail_755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList(lean_object* v_00_u03b1_760_, lean_object* v_00_u03b2_761_, lean_object* v_inst_762_, lean_object* v_l_763_, lean_object* v_toInsert_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_Internal_List_insertList___redArg(v_inst_762_, v_l_763_, v_toInsert_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew___redArg(lean_object* v_inst_766_, lean_object* v_l_767_, lean_object* v_toInsert_768_){
_start:
{
if (lean_obj_tag(v_toInsert_768_) == 0)
{
lean_dec_ref(v_inst_766_);
return v_l_767_;
}
else
{
lean_object* v_head_769_; lean_object* v_tail_770_; lean_object* v_fst_771_; lean_object* v_snd_772_; lean_object* v___x_773_; 
v_head_769_ = lean_ctor_get(v_toInsert_768_, 0);
lean_inc(v_head_769_);
v_tail_770_ = lean_ctor_get(v_toInsert_768_, 1);
lean_inc(v_tail_770_);
lean_dec_ref(v_toInsert_768_);
v_fst_771_ = lean_ctor_get(v_head_769_, 0);
lean_inc(v_fst_771_);
v_snd_772_ = lean_ctor_get(v_head_769_, 1);
lean_inc(v_snd_772_);
lean_dec(v_head_769_);
lean_inc_ref(v_inst_766_);
v___x_773_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_766_, v_fst_771_, v_snd_772_, v_l_767_);
v_l_767_ = v___x_773_;
v_toInsert_768_ = v_tail_770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew(lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v_inst_777_, lean_object* v_l_778_, lean_object* v_toInsert_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Std_Internal_List_insertListIfNew___redArg(v_inst_777_, v_l_778_, v_toInsert_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList___redArg(lean_object* v_inst_781_, lean_object* v_l_u2081_782_, lean_object* v_l_u2082_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_784_ = l_List_lengthTR___redArg(v_l_u2081_782_);
v___x_785_ = l_List_lengthTR___redArg(v_l_u2082_783_);
v___x_786_ = lean_nat_dec_le(v___x_784_, v___x_785_);
lean_dec(v___x_785_);
lean_dec(v___x_784_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_Internal_List_insertList___redArg(v_inst_781_, v_l_u2081_782_, v_l_u2082_783_);
return v___x_787_;
}
else
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_Internal_List_insertListIfNew___redArg(v_inst_781_, v_l_u2082_783_, v_l_u2081_782_);
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList(lean_object* v_00_u03b1_789_, lean_object* v_00_u03b2_790_, lean_object* v_inst_791_, lean_object* v_l_u2081_792_, lean_object* v_l_u2082_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_Internal_List_insertSmallerList___redArg(v_inst_791_, v_l_u2081_792_, v_l_u2082_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma___redArg(lean_object* v_p_795_){
_start:
{
lean_object* v_fst_796_; lean_object* v_snd_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_fst_796_ = lean_ctor_get(v_p_795_, 0);
v_snd_797_ = lean_ctor_get(v_p_795_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_p_795_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v_p_795_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_snd_797_);
lean_inc(v_fst_796_);
lean_dec(v_p_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_fst_796_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_snd_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma(lean_object* v_00_u03b1_805_, lean_object* v_00_u03b2_806_, lean_object* v_p_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_Internal_List_Prod_toSigma___redArg(v_p_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst___redArg(lean_object* v_inst_810_, lean_object* v_l_811_, lean_object* v_toInsert_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_813_ = ((lean_object*)(l_Std_Internal_List_insertListConst___redArg___closed__0));
v___x_814_ = lean_box(0);
v___x_815_ = l_List_mapTR_loop___redArg(v___x_813_, v_toInsert_812_, v___x_814_);
v___x_816_ = l_Std_Internal_List_insertList___redArg(v_inst_810_, v_l_811_, v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst(lean_object* v_00_u03b1_817_, lean_object* v_00_u03b2_818_, lean_object* v_inst_819_, lean_object* v_l_820_, lean_object* v_toInsert_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_Internal_List_insertListConst___redArg(v_inst_819_, v_l_820_, v_toInsert_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit___redArg(lean_object* v_inst_823_, lean_object* v_l_824_, lean_object* v_toInsert_825_){
_start:
{
if (lean_obj_tag(v_toInsert_825_) == 0)
{
lean_dec_ref(v_inst_823_);
return v_l_824_;
}
else
{
lean_object* v_head_826_; lean_object* v_tail_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_head_826_ = lean_ctor_get(v_toInsert_825_, 0);
lean_inc(v_head_826_);
v_tail_827_ = lean_ctor_get(v_toInsert_825_, 1);
lean_inc(v_tail_827_);
lean_dec_ref(v_toInsert_825_);
v___x_828_ = lean_box(0);
lean_inc_ref(v_inst_823_);
v___x_829_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_823_, v_head_826_, v___x_828_, v_l_824_);
v_l_824_ = v___x_829_;
v_toInsert_825_ = v_tail_827_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit(lean_object* v_00_u03b1_831_, lean_object* v_inst_832_, lean_object* v_l_833_, lean_object* v_toInsert_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_Internal_List_insertListIfNewUnit___redArg(v_inst_832_, v_l_833_, v_toInsert_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(lean_object* v_toInsert_836_, lean_object* v_h__1_837_, lean_object* v_h__2_838_){
_start:
{
if (lean_obj_tag(v_toInsert_836_) == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v_h__2_838_);
v___x_839_ = lean_box(0);
v___x_840_ = lean_apply_1(v_h__1_837_, v___x_839_);
return v___x_840_;
}
else
{
lean_object* v_head_841_; lean_object* v_tail_842_; lean_object* v___x_843_; 
lean_dec(v_h__1_837_);
v_head_841_ = lean_ctor_get(v_toInsert_836_, 0);
lean_inc(v_head_841_);
v_tail_842_ = lean_ctor_get(v_toInsert_836_, 1);
lean_inc(v_tail_842_);
lean_dec_ref(v_toInsert_836_);
v___x_843_ = lean_apply_2(v_h__2_838_, v_head_841_, v_tail_842_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object* v_00_u03b1_844_, lean_object* v_motive_845_, lean_object* v_toInsert_846_, lean_object* v_h__1_847_, lean_object* v_h__2_848_){
_start:
{
if (lean_obj_tag(v_toInsert_846_) == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v_h__2_848_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_apply_1(v_h__1_847_, v___x_849_);
return v___x_850_;
}
else
{
lean_object* v_head_851_; lean_object* v_tail_852_; lean_object* v___x_853_; 
lean_dec(v_h__1_847_);
v_head_851_ = lean_ctor_get(v_toInsert_846_, 0);
lean_inc(v_head_851_);
v_tail_852_ = lean_ctor_get(v_toInsert_846_, 1);
lean_inc(v_tail_852_);
lean_dec_ref(v_toInsert_846_);
v___x_853_ = lean_apply_2(v_h__2_848_, v_head_851_, v_tail_852_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey___redArg(lean_object* v_inst_854_, lean_object* v_k_855_, lean_object* v_f_856_, lean_object* v_l_857_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
lean_inc(v_l_857_);
lean_inc(v_k_855_);
lean_inc_ref(v_inst_854_);
v___x_858_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_854_, v_k_855_, v_l_857_);
v___x_859_ = lean_apply_1(v_f_856_, v___x_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_Internal_List_eraseKey___redArg(v_inst_854_, v_k_855_, v_l_857_);
return v___x_860_;
}
else
{
lean_object* v_val_861_; lean_object* v___x_862_; 
v_val_861_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_val_861_);
lean_dec_ref(v___x_859_);
v___x_862_ = l_Std_Internal_List_insertEntry___redArg(v_inst_854_, v_k_855_, v_val_861_, v_l_857_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_k_867_, lean_object* v_f_868_, lean_object* v_l_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_Internal_List_alterKey___redArg(v_inst_865_, v_k_867_, v_f_868_, v_l_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object* v_x_871_, lean_object* v_h__1_872_, lean_object* v_h__2_873_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec(v_h__2_873_);
v___x_874_ = lean_box(0);
v___x_875_ = lean_apply_1(v_h__1_872_, v___x_874_);
return v___x_875_;
}
else
{
lean_object* v_val_876_; lean_object* v___x_877_; 
lean_dec(v_h__1_872_);
v_val_876_ = lean_ctor_get(v_x_871_, 0);
lean_inc(v_val_876_);
lean_dec_ref(v_x_871_);
v___x_877_ = lean_apply_1(v_h__2_873_, v_val_876_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* v_00_u03b1_878_, lean_object* v_00_u03b2_879_, lean_object* v_k_880_, lean_object* v_motive_881_, lean_object* v_x_882_, lean_object* v_h__1_883_, lean_object* v_h__2_884_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec(v_h__2_884_);
v___x_885_ = lean_box(0);
v___x_886_ = lean_apply_1(v_h__1_883_, v___x_885_);
return v___x_886_;
}
else
{
lean_object* v_val_887_; lean_object* v___x_888_; 
lean_dec(v_h__1_883_);
v_val_887_ = lean_ctor_get(v_x_882_, 0);
lean_inc(v_val_887_);
lean_dec_ref(v_x_882_);
v___x_888_ = lean_apply_1(v_h__2_884_, v_val_887_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* v_00_u03b1_889_, lean_object* v_00_u03b2_890_, lean_object* v_k_891_, lean_object* v_motive_892_, lean_object* v_x_893_, lean_object* v_h__1_894_, lean_object* v_h__2_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_889_, v_00_u03b2_890_, v_k_891_, v_motive_892_, v_x_893_, v_h__1_894_, v_h__2_895_);
lean_dec(v_k_891_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_897_, lean_object* v_h__1_898_, lean_object* v_h__2_899_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_h__2_899_);
v___x_900_ = lean_box(0);
v___x_901_ = lean_apply_1(v_h__1_898_, v___x_900_);
return v___x_901_;
}
else
{
lean_object* v_val_902_; lean_object* v___x_903_; 
lean_dec(v_h__1_898_);
v_val_902_ = lean_ctor_get(v_x_897_, 0);
lean_inc(v_val_902_);
lean_dec_ref(v_x_897_);
v___x_903_ = lean_apply_1(v_h__2_899_, v_val_902_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_904_, lean_object* v_00_u03b2_905_, lean_object* v_k_906_, lean_object* v_motive_907_, lean_object* v_x_908_, lean_object* v_h__1_909_, lean_object* v_h__2_910_){
_start:
{
if (lean_obj_tag(v_x_908_) == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec(v_h__2_910_);
v___x_911_ = lean_box(0);
v___x_912_ = lean_apply_1(v_h__1_909_, v___x_911_);
return v___x_912_;
}
else
{
lean_object* v_val_913_; lean_object* v___x_914_; 
lean_dec(v_h__1_909_);
v_val_913_ = lean_ctor_get(v_x_908_, 0);
lean_inc(v_val_913_);
lean_dec_ref(v_x_908_);
v___x_914_ = lean_apply_1(v_h__2_910_, v_val_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_915_, lean_object* v_00_u03b2_916_, lean_object* v_k_917_, lean_object* v_motive_918_, lean_object* v_x_919_, lean_object* v_h__1_920_, lean_object* v_h__2_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_915_, v_00_u03b2_916_, v_k_917_, v_motive_918_, v_x_919_, v_h__1_920_, v_h__2_921_);
lean_dec(v_k_917_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey___redArg(lean_object* v_inst_923_, lean_object* v_k_924_, lean_object* v_f_925_, lean_object* v_l_926_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_inc(v_l_926_);
lean_inc(v_k_924_);
lean_inc_ref(v_inst_923_);
v___x_927_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_923_, v_k_924_, v_l_926_);
v___x_928_ = lean_apply_1(v_f_925_, v___x_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_929_; 
v___x_929_ = l_Std_Internal_List_eraseKey___redArg(v_inst_923_, v_k_924_, v_l_926_);
return v___x_929_;
}
else
{
lean_object* v_val_930_; lean_object* v___x_931_; 
v_val_930_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_val_930_);
lean_dec_ref(v___x_928_);
v___x_931_ = l_Std_Internal_List_insertEntry___redArg(v_inst_923_, v_k_924_, v_val_930_, v_l_926_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey(lean_object* v_00_u03b1_932_, lean_object* v_00_u03b2_933_, lean_object* v_inst_934_, lean_object* v_k_935_, lean_object* v_f_936_, lean_object* v_l_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Std_Internal_List_Const_alterKey___redArg(v_inst_934_, v_k_935_, v_f_936_, v_l_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object* v_x_939_, lean_object* v_h__1_940_, lean_object* v_h__2_941_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_h__2_941_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_apply_1(v_h__1_940_, v___x_942_);
return v___x_943_;
}
else
{
lean_object* v_val_944_; lean_object* v___x_945_; 
lean_dec(v_h__1_940_);
v_val_944_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_val_944_);
lean_dec_ref(v_x_939_);
v___x_945_ = lean_apply_1(v_h__2_941_, v_val_944_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* v_00_u03b2_946_, lean_object* v_motive_947_, lean_object* v_x_948_, lean_object* v_h__1_949_, lean_object* v_h__2_950_){
_start:
{
if (lean_obj_tag(v_x_948_) == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_h__2_950_);
v___x_951_ = lean_box(0);
v___x_952_ = lean_apply_1(v_h__1_949_, v___x_951_);
return v___x_952_;
}
else
{
lean_object* v_val_953_; lean_object* v___x_954_; 
lean_dec(v_h__1_949_);
v_val_953_ = lean_ctor_get(v_x_948_, 0);
lean_inc(v_val_953_);
lean_dec_ref(v_x_948_);
v___x_954_ = lean_apply_1(v_h__2_950_, v_val_953_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_955_, lean_object* v_h__1_956_, lean_object* v_h__2_957_){
_start:
{
if (lean_obj_tag(v_x_955_) == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v_h__2_957_);
v___x_958_ = lean_box(0);
v___x_959_ = lean_apply_1(v_h__1_956_, v___x_958_);
return v___x_959_;
}
else
{
lean_object* v_val_960_; lean_object* v___x_961_; 
lean_dec(v_h__1_956_);
v_val_960_ = lean_ctor_get(v_x_955_, 0);
lean_inc(v_val_960_);
lean_dec_ref(v_x_955_);
v___x_961_ = lean_apply_1(v_h__2_957_, v_val_960_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b2_962_, lean_object* v_motive_963_, lean_object* v_x_964_, lean_object* v_h__1_965_, lean_object* v_h__2_966_){
_start:
{
if (lean_obj_tag(v_x_964_) == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_h__2_966_);
v___x_967_ = lean_box(0);
v___x_968_ = lean_apply_1(v_h__1_965_, v___x_967_);
return v___x_968_;
}
else
{
lean_object* v_val_969_; lean_object* v___x_970_; 
lean_dec(v_h__1_965_);
v_val_969_ = lean_ctor_get(v_x_964_, 0);
lean_inc(v_val_969_);
lean_dec_ref(v_x_964_);
v___x_970_ = lean_apply_1(v_h__2_966_, v_val_969_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey___redArg(lean_object* v_inst_971_, lean_object* v_k_972_, lean_object* v_f_973_, lean_object* v_l_974_){
_start:
{
lean_object* v___x_975_; 
lean_inc(v_l_974_);
lean_inc(v_k_972_);
lean_inc_ref(v_inst_971_);
v___x_975_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_971_, v_k_972_, v_l_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_dec(v_f_973_);
lean_dec(v_k_972_);
lean_dec_ref(v_inst_971_);
return v_l_974_;
}
else
{
lean_object* v_val_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_val_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_val_976_);
lean_dec_ref(v___x_975_);
v___x_977_ = lean_apply_1(v_f_973_, v_val_976_);
v___x_978_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_971_, v_k_972_, v___x_977_, v_l_974_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey(lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_k_983_, lean_object* v_f_984_, lean_object* v_l_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_Internal_List_modifyKey___redArg(v_inst_981_, v_k_983_, v_f_984_, v_l_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey___redArg(lean_object* v_inst_987_, lean_object* v_k_988_, lean_object* v_f_989_, lean_object* v_l_990_){
_start:
{
lean_object* v___x_991_; 
lean_inc(v_l_990_);
lean_inc(v_k_988_);
lean_inc_ref(v_inst_987_);
v___x_991_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_987_, v_k_988_, v_l_990_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_dec(v_f_989_);
lean_dec(v_k_988_);
lean_dec_ref(v_inst_987_);
return v_l_990_;
}
else
{
lean_object* v_val_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_val_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_val_992_);
lean_dec_ref(v___x_991_);
v___x_993_ = lean_apply_1(v_f_989_, v_val_992_);
v___x_994_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_987_, v_k_988_, v___x_993_, v_l_990_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey(lean_object* v_00_u03b1_995_, lean_object* v_00_u03b2_996_, lean_object* v_inst_997_, lean_object* v_k_998_, lean_object* v_f_999_, lean_object* v_l_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Std_Internal_List_Const_modifyKey___redArg(v_inst_997_, v_k_998_, v_f_999_, v_l_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_1002_, lean_object* v_h__1_1003_, lean_object* v_h__2_1004_){
_start:
{
if (lean_obj_tag(v_x_1002_) == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec(v_h__1_1003_);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_apply_1(v_h__2_1004_, v___x_1005_);
return v___x_1006_;
}
else
{
lean_object* v_val_1007_; lean_object* v___x_1008_; 
lean_dec(v_h__2_1004_);
v_val_1007_ = lean_ctor_get(v_x_1002_, 0);
lean_inc(v_val_1007_);
lean_dec_ref(v_x_1002_);
v___x_1008_ = lean_apply_1(v_h__1_1003_, v_val_1007_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_1009_, lean_object* v_motive_1010_, lean_object* v_x_1011_, lean_object* v_h__1_1012_, lean_object* v_h__2_1013_){
_start:
{
if (lean_obj_tag(v_x_1011_) == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec(v_h__1_1012_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_apply_1(v_h__2_1013_, v___x_1014_);
return v___x_1015_;
}
else
{
lean_object* v_val_1016_; lean_object* v___x_1017_; 
lean_dec(v_h__2_1013_);
v_val_1016_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_val_1016_);
lean_dec_ref(v_x_1011_);
v___x_1017_ = lean_apply_1(v_h__1_1012_, v_val_1016_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList___redArg(lean_object* v_inst_1018_, lean_object* v_l_1019_, lean_object* v_toErase_1020_){
_start:
{
if (lean_obj_tag(v_toErase_1020_) == 0)
{
lean_dec_ref(v_inst_1018_);
return v_l_1019_;
}
else
{
lean_object* v_head_1021_; lean_object* v_tail_1022_; lean_object* v___x_1023_; 
v_head_1021_ = lean_ctor_get(v_toErase_1020_, 0);
lean_inc(v_head_1021_);
v_tail_1022_ = lean_ctor_get(v_toErase_1020_, 1);
lean_inc(v_tail_1022_);
lean_dec_ref(v_toErase_1020_);
lean_inc_ref(v_inst_1018_);
v___x_1023_ = l_Std_Internal_List_eraseKey___redArg(v_inst_1018_, v_head_1021_, v_l_1019_);
v_l_1019_ = v___x_1023_;
v_toErase_1020_ = v_tail_1022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_inst_1027_, lean_object* v_l_1028_, lean_object* v_toErase_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Std_Internal_List_eraseList___redArg(v_inst_1027_, v_l_1028_, v_toErase_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_1031_, lean_object* v_h__1_1032_, lean_object* v_h__2_1033_){
_start:
{
if (lean_obj_tag(v_opt_1031_) == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec(v_h__1_1032_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_apply_1(v_h__2_1033_, v___x_1034_);
return v___x_1035_;
}
else
{
lean_object* v_val_1036_; lean_object* v___x_1037_; 
lean_dec(v_h__2_1033_);
v_val_1036_ = lean_ctor_get(v_opt_1031_, 0);
lean_inc(v_val_1036_);
lean_dec_ref(v_opt_1031_);
v___x_1037_ = lean_apply_1(v_h__1_1032_, v_val_1036_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_1038_, lean_object* v_motive_1039_, lean_object* v_opt_1040_, lean_object* v_h__1_1041_, lean_object* v_h__2_1042_){
_start:
{
if (lean_obj_tag(v_opt_1040_) == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v_h__1_1041_);
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_apply_1(v_h__2_1042_, v___x_1043_);
return v___x_1044_;
}
else
{
lean_object* v_val_1045_; lean_object* v___x_1046_; 
lean_dec(v_h__2_1042_);
v_val_1045_ = lean_ctor_get(v_opt_1040_, 0);
lean_inc(v_val_1045_);
lean_dec_ref(v_opt_1040_);
v___x_1046_ = lean_apply_1(v_h__1_1041_, v_val_1045_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(lean_object* v_00_u03b1_1047_, lean_object* v_00_u03b2_1048_, lean_object* v_inst_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_box(0);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___boxed(lean_object* v_00_u03b1_1051_, lean_object* v_00_u03b2_1052_, lean_object* v_inst_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(v_00_u03b1_1051_, v_00_u03b2_1052_, v_inst_1053_);
lean_dec_ref(v_inst_1053_);
return v_res_1054_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(lean_object* v_inst_1055_, lean_object* v_a_1056_, lean_object* v_b_1057_){
_start:
{
lean_object* v_fst_1058_; lean_object* v_fst_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_fst_1058_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_fst_1058_);
lean_dec_ref(v_a_1056_);
v_fst_1059_ = lean_ctor_get(v_b_1057_, 0);
lean_inc(v_fst_1059_);
lean_dec_ref(v_b_1057_);
v___x_1060_ = lean_apply_2(v_inst_1055_, v_fst_1058_, v_fst_1059_);
v___x_1061_ = lean_unbox(v___x_1060_);
if (v___x_1061_ == 2)
{
uint8_t v___x_1062_; 
v___x_1062_ = 0;
return v___x_1062_;
}
else
{
uint8_t v___x_1063_; 
v___x_1063_ = 1;
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg___boxed(lean_object* v_inst_1064_, lean_object* v_a_1065_, lean_object* v_b_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_1064_, v_a_1065_, v_b_1066_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(lean_object* v_00_u03b1_1069_, lean_object* v_00_u03b2_1070_, lean_object* v_inst_1071_, lean_object* v_a_1072_, lean_object* v_b_1073_){
_start:
{
uint8_t v___x_1074_; 
v___x_1074_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_1071_, v_a_1072_, v_b_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_00_u03b2_1076_, lean_object* v_inst_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_){
_start:
{
uint8_t v_res_1080_; lean_object* v_r_1081_; 
v_res_1080_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(v_00_u03b1_1075_, v_00_u03b2_1076_, v_inst_1077_, v_a_1078_, v_b_1079_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0(lean_object* v_inst_1082_, lean_object* v_a_1083_, lean_object* v_b_1084_){
_start:
{
lean_object* v_fst_1085_; lean_object* v_fst_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_fst_1085_ = lean_ctor_get(v_a_1083_, 0);
v_fst_1086_ = lean_ctor_get(v_b_1084_, 0);
lean_inc(v_fst_1086_);
lean_inc(v_fst_1085_);
v___x_1087_ = lean_apply_2(v_inst_1082_, v_fst_1085_, v_fst_1086_);
v___x_1088_ = lean_unbox(v___x_1087_);
if (v___x_1088_ == 2)
{
lean_dec_ref(v_a_1083_);
return v_b_1084_;
}
else
{
lean_dec_ref(v_b_1084_);
return v_a_1083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg(lean_object* v_inst_1089_){
_start:
{
lean_object* v___f_1090_; 
v___f_1090_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1090_, 0, v_inst_1089_);
return v___f_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd(lean_object* v_00_u03b1_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_inst_1093_){
_start:
{
lean_object* v___f_1094_; 
v___f_1094_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1094_, 0, v_inst_1093_);
return v___f_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___redArg(lean_object* v_inst_1095_, lean_object* v_xs_1096_){
_start:
{
lean_object* v___f_1097_; lean_object* v___x_1098_; 
v___f_1097_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1097_, 0, v_inst_1095_);
v___x_1098_ = l_List_min_x3f___redArg(v___f_1097_, v_xs_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f(lean_object* v_00_u03b1_1099_, lean_object* v_00_u03b2_1100_, lean_object* v_inst_1101_, lean_object* v_xs_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_1101_, v_xs_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___redArg(lean_object* v_inst_1104_, lean_object* v_xs_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_1104_, v_xs_1105_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_box(0);
return v___x_1107_;
}
else
{
lean_object* v_val_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1116_; 
v_val_1108_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1110_ = v___x_1106_;
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_val_1108_);
lean_dec(v___x_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v_fst_1112_; lean_object* v___x_1114_; 
v_fst_1112_ = lean_ctor_get(v_val_1108_, 0);
lean_inc(v_fst_1112_);
lean_dec(v_val_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v_fst_1112_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_fst_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f(lean_object* v_00_u03b1_1117_, lean_object* v_00_u03b2_1118_, lean_object* v_inst_1119_, lean_object* v_xs_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1119_, v_xs_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___redArg(lean_object* v_x_1122_, lean_object* v_h__1_1123_, lean_object* v_h__2_1124_){
_start:
{
if (lean_obj_tag(v_x_1122_) == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v_h__2_1124_);
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_apply_1(v_h__1_1123_, v___x_1125_);
return v___x_1126_;
}
else
{
lean_object* v_val_1127_; lean_object* v___x_1128_; 
lean_dec(v_h__1_1123_);
v_val_1127_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_val_1127_);
lean_dec_ref(v_x_1122_);
v___x_1128_ = lean_apply_1(v_h__2_1124_, v_val_1127_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_motive_1131_, lean_object* v_x_1132_, lean_object* v_h__1_1133_, lean_object* v_h__2_1134_){
_start:
{
if (lean_obj_tag(v_x_1132_) == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v_h__2_1134_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_apply_1(v_h__1_1133_, v___x_1135_);
return v___x_1136_;
}
else
{
lean_object* v_val_1137_; lean_object* v___x_1138_; 
lean_dec(v_h__1_1133_);
v_val_1137_ = lean_ctor_get(v_x_1132_, 0);
lean_inc(v_val_1137_);
lean_dec_ref(v_x_1132_);
v___x_1138_ = lean_apply_1(v_h__2_1134_, v_val_1137_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_1139_, lean_object* v_h__1_1140_, lean_object* v_h__2_1141_){
_start:
{
if (lean_obj_tag(v_x_1139_) == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec(v_h__2_1141_);
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_apply_1(v_h__1_1140_, v___x_1142_);
return v___x_1143_;
}
else
{
lean_object* v_head_1144_; lean_object* v_tail_1145_; lean_object* v___x_1146_; 
lean_dec(v_h__1_1140_);
v_head_1144_ = lean_ctor_get(v_x_1139_, 0);
lean_inc(v_head_1144_);
v_tail_1145_ = lean_ctor_get(v_x_1139_, 1);
lean_inc(v_tail_1145_);
lean_dec_ref(v_x_1139_);
v___x_1146_ = lean_apply_2(v_h__2_1141_, v_head_1144_, v_tail_1145_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_1147_, lean_object* v_motive_1148_, lean_object* v_x_1149_, lean_object* v_h__1_1150_, lean_object* v_h__2_1151_){
_start:
{
if (lean_obj_tag(v_x_1149_) == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v_h__2_1151_);
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_apply_1(v_h__1_1150_, v___x_1152_);
return v___x_1153_;
}
else
{
lean_object* v_head_1154_; lean_object* v_tail_1155_; lean_object* v___x_1156_; 
lean_dec(v_h__1_1150_);
v_head_1154_ = lean_ctor_get(v_x_1149_, 0);
lean_inc(v_head_1154_);
v_tail_1155_ = lean_ctor_get(v_x_1149_, 1);
lean_inc(v_tail_1155_);
lean_dec_ref(v_x_1149_);
v___x_1156_ = lean_apply_2(v_h__2_1151_, v_head_1154_, v_tail_1155_);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter___redArg(lean_object* v_x_1157_, lean_object* v_h__1_1158_, lean_object* v_h__2_1159_){
_start:
{
if (lean_obj_tag(v_x_1157_) == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_h__2_1159_);
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_apply_1(v_h__1_1158_, v___x_1160_);
return v___x_1161_;
}
else
{
lean_object* v_val_1162_; lean_object* v___x_1163_; 
lean_dec(v_h__1_1158_);
v_val_1162_ = lean_ctor_get(v_x_1157_, 0);
lean_inc(v_val_1162_);
lean_dec_ref(v_x_1157_);
v___x_1163_ = lean_apply_1(v_h__2_1159_, v_val_1162_);
return v___x_1163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter(lean_object* v_00_u03b1_1164_, lean_object* v_00_u03b2_1165_, lean_object* v_motive_1166_, lean_object* v_x_1167_, lean_object* v_h__1_1168_, lean_object* v_h__2_1169_){
_start:
{
if (lean_obj_tag(v_x_1167_) == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v_h__2_1169_);
v___x_1170_ = lean_box(0);
v___x_1171_ = lean_apply_1(v_h__1_1168_, v___x_1170_);
return v___x_1171_;
}
else
{
lean_object* v_val_1172_; lean_object* v___x_1173_; 
lean_dec(v_h__1_1168_);
v_val_1172_ = lean_ctor_get(v_x_1167_, 0);
lean_inc(v_val_1172_);
lean_dec_ref(v_x_1167_);
v___x_1173_ = lean_apply_1(v_h__2_1169_, v_val_1172_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___redArg(lean_object* v_inst_1174_, lean_object* v_xs_1175_){
_start:
{
lean_object* v___x_1176_; lean_object* v_val_1177_; 
v___x_1176_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1174_, v_xs_1175_);
v_val_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_val_1177_);
lean_dec(v___x_1176_);
return v_val_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey(lean_object* v_00_u03b1_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_inst_1180_, lean_object* v_xs_1181_, lean_object* v_h_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Std_Internal_List_minKey___redArg(v_inst_1180_, v_xs_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___redArg(lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_xs_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1184_, v_xs_1186_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_1189_ = l_panic___redArg(v_inst_1185_, v___x_1188_);
return v___x_1189_;
}
else
{
lean_object* v_val_1190_; 
v_val_1190_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_val_1190_);
lean_dec_ref(v___x_1187_);
return v_val_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___redArg___boxed(lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_xs_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_1191_, v_inst_1192_, v_xs_1193_);
lean_dec(v_inst_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21(lean_object* v_00_u03b1_1195_, lean_object* v_00_u03b2_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_xs_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_1197_, v_inst_1198_, v_xs_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___boxed(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_xs_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Std_Internal_List_minKey_x21(v_00_u03b1_1201_, v_00_u03b2_1202_, v_inst_1203_, v_inst_1204_, v_xs_1205_);
lean_dec(v_inst_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg(lean_object* v_inst_1207_, lean_object* v_xs_1208_, lean_object* v_fallback_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1207_, v_xs_1208_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_inc(v_fallback_1209_);
return v_fallback_1209_;
}
else
{
lean_object* v_val_1211_; 
v_val_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_val_1211_);
lean_dec_ref(v___x_1210_);
return v_val_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg___boxed(lean_object* v_inst_1212_, lean_object* v_xs_1213_, lean_object* v_fallback_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Std_Internal_List_minKeyD___redArg(v_inst_1212_, v_xs_1213_, v_fallback_1214_);
lean_dec(v_fallback_1214_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD(lean_object* v_00_u03b1_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_inst_1218_, lean_object* v_xs_1219_, lean_object* v_fallback_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Std_Internal_List_minKeyD___redArg(v_inst_1218_, v_xs_1219_, v_fallback_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___boxed(lean_object* v_00_u03b1_1222_, lean_object* v_00_u03b2_1223_, lean_object* v_inst_1224_, lean_object* v_xs_1225_, lean_object* v_fallback_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Std_Internal_List_minKeyD(v_00_u03b1_1222_, v_00_u03b2_1223_, v_inst_1224_, v_xs_1225_, v_fallback_1226_);
lean_dec(v_fallback_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f___redArg(lean_object* v_inst_1228_, lean_object* v_xs_1229_){
_start:
{
lean_object* v___f_1230_; lean_object* v___x_1231_; 
v___f_1230_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1230_, 0, v_inst_1228_);
v___x_1231_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1230_, v_xs_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f(lean_object* v_00_u03b1_1232_, lean_object* v_00_u03b2_1233_, lean_object* v_inst_1234_, lean_object* v_xs_1235_){
_start:
{
lean_object* v___f_1236_; lean_object* v___x_1237_; 
v___f_1236_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1236_, 0, v_inst_1234_);
v___x_1237_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1236_, v_xs_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey___redArg(lean_object* v_inst_1238_, lean_object* v_xs_1239_){
_start:
{
lean_object* v___f_1240_; lean_object* v___x_1241_; 
v___f_1240_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1240_, 0, v_inst_1238_);
v___x_1241_ = l_Std_Internal_List_minKey___redArg(v___f_1240_, v_xs_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey(lean_object* v_00_u03b1_1242_, lean_object* v_00_u03b2_1243_, lean_object* v_inst_1244_, lean_object* v_xs_1245_, lean_object* v_h_1246_){
_start:
{
lean_object* v___f_1247_; lean_object* v___x_1248_; 
v___f_1247_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1247_, 0, v_inst_1244_);
v___x_1248_ = l_Std_Internal_List_minKey___redArg(v___f_1247_, v_xs_1245_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg(lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_xs_1251_){
_start:
{
lean_object* v___f_1252_; lean_object* v___x_1253_; 
v___f_1252_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1252_, 0, v_inst_1249_);
v___x_1253_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1252_, v_xs_1251_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_1255_ = l_panic___redArg(v_inst_1250_, v___x_1254_);
return v___x_1255_;
}
else
{
lean_object* v_val_1256_; 
v_val_1256_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_val_1256_);
lean_dec_ref(v___x_1253_);
return v_val_1256_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg___boxed(lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_xs_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_1257_, v_inst_1258_, v_xs_1259_);
lean_dec(v_inst_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_xs_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_1263_, v_inst_1264_, v_xs_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_00_u03b2_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_xs_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Std_Internal_List_maxKey_x21(v_00_u03b1_1267_, v_00_u03b2_1268_, v_inst_1269_, v_inst_1270_, v_xs_1271_);
lean_dec(v_inst_1270_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg(lean_object* v_inst_1273_, lean_object* v_xs_1274_, lean_object* v_fallback_1275_){
_start:
{
lean_object* v___f_1276_; lean_object* v___x_1277_; 
v___f_1276_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1276_, 0, v_inst_1273_);
v___x_1277_ = l_Std_Internal_List_minKeyD___redArg(v___f_1276_, v_xs_1274_, v_fallback_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg___boxed(lean_object* v_inst_1278_, lean_object* v_xs_1279_, lean_object* v_fallback_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_Internal_List_maxKeyD___redArg(v_inst_1278_, v_xs_1279_, v_fallback_1280_);
lean_dec(v_fallback_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD(lean_object* v_00_u03b1_1282_, lean_object* v_00_u03b2_1283_, lean_object* v_inst_1284_, lean_object* v_xs_1285_, lean_object* v_fallback_1286_){
_start:
{
lean_object* v___f_1287_; lean_object* v___x_1288_; 
v___f_1287_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1287_, 0, v_inst_1284_);
v___x_1288_ = l_Std_Internal_List_minKeyD___redArg(v___f_1287_, v_xs_1285_, v_fallback_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_inst_1291_, lean_object* v_xs_1292_, lean_object* v_fallback_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Std_Internal_List_maxKeyD(v_00_u03b1_1289_, v_00_u03b2_1290_, v_inst_1291_, v_xs_1292_, v_fallback_1293_);
lean_dec(v_fallback_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn___redArg(lean_object* v_inst_1295_, lean_object* v_l_1296_, lean_object* v_sofar_1297_, lean_object* v_k_1298_){
_start:
{
lean_object* v___x_1299_; 
lean_inc_ref(v_inst_1295_);
v___x_1299_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_1295_, v_k_1298_, v_l_1296_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_dec_ref(v_inst_1295_);
return v_sofar_1297_;
}
else
{
lean_object* v_val_1300_; lean_object* v_fst_1301_; lean_object* v_snd_1302_; lean_object* v___x_1303_; 
v_val_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_val_1300_);
lean_dec_ref(v___x_1299_);
v_fst_1301_ = lean_ctor_get(v_val_1300_, 0);
lean_inc(v_fst_1301_);
v_snd_1302_ = lean_ctor_get(v_val_1300_, 1);
lean_inc(v_snd_1302_);
lean_dec(v_val_1300_);
v___x_1303_ = l_Std_Internal_List_insertEntry___redArg(v_inst_1295_, v_fst_1301_, v_snd_1302_, v_sofar_1297_);
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn(lean_object* v_00_u03b1_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_inst_1306_, lean_object* v_l_1307_, lean_object* v_sofar_1308_, lean_object* v_k_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Std_Internal_List_interSmallerFn___redArg(v_inst_1306_, v_l_1307_, v_sofar_1308_, v_k_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_1311_, lean_object* v_h__1_1312_, lean_object* v_h__2_1313_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_h__1_1312_);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_apply_1(v_h__2_1313_, v___x_1314_);
return v___x_1315_;
}
else
{
lean_object* v_val_1316_; lean_object* v___x_1317_; 
lean_dec(v_h__2_1313_);
v_val_1316_ = lean_ctor_get(v_x_1311_, 0);
lean_inc(v_val_1316_);
lean_dec_ref(v_x_1311_);
v___x_1317_ = lean_apply_1(v_h__1_1312_, v_val_1316_);
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_1318_, lean_object* v_00_u03b2_1319_, lean_object* v_motive_1320_, lean_object* v_x_1321_, lean_object* v_h__1_1322_, lean_object* v_h__2_1323_){
_start:
{
if (lean_obj_tag(v_x_1321_) == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec(v_h__1_1322_);
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_apply_1(v_h__2_1323_, v___x_1324_);
return v___x_1325_;
}
else
{
lean_object* v_val_1326_; lean_object* v___x_1327_; 
lean_dec(v_h__2_1323_);
v_val_1326_ = lean_ctor_get(v_x_1321_, 0);
lean_inc(v_val_1326_);
lean_dec_ref(v_x_1321_);
v___x_1327_ = lean_apply_1(v_h__1_1322_, v_val_1326_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg___lam__0(lean_object* v_inst_1328_, lean_object* v_l_u2081_1329_, lean_object* v_sofar_1330_, lean_object* v_kv_1331_){
_start:
{
lean_object* v_fst_1332_; lean_object* v___x_1333_; 
v_fst_1332_ = lean_ctor_get(v_kv_1331_, 0);
lean_inc(v_fst_1332_);
lean_dec_ref(v_kv_1331_);
v___x_1333_ = l_Std_Internal_List_interSmallerFn___redArg(v_inst_1328_, v_l_u2081_1329_, v_sofar_1330_, v_fst_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg(lean_object* v_inst_1334_, lean_object* v_l_u2081_1335_, lean_object* v_l_u2082_1336_){
_start:
{
lean_object* v___f_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___f_1337_ = lean_alloc_closure((void*)(l_Std_Internal_List_interSmaller___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1337_, 0, v_inst_1334_);
lean_closure_set(v___f_1337_, 1, v_l_u2081_1335_);
v___x_1338_ = lean_box(0);
v___x_1339_ = l_List_foldl___redArg(v___f_1337_, v___x_1338_, v_l_u2082_1336_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller(lean_object* v_00_u03b1_1340_, lean_object* v_00_u03b2_1341_, lean_object* v_inst_1342_, lean_object* v_l_u2081_1343_, lean_object* v_l_u2082_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Std_Internal_List_interSmaller___redArg(v_inst_1342_, v_l_u2081_1343_, v_l_u2082_1344_);
return v___x_1345_;
}
}
lean_object* runtime_initialize_Init_Data_Option_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Perm(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Internal_List_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Internal_List_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_LemmasExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Internal_List_Associative(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Option_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_LemmasExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Internal_List_Associative(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Option_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_List_Perm(uint8_t builtin);
lean_object* initialize_Std_Data_Internal_List_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_Internal_List_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_Order_LemmasExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Internal_List_Associative(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Internal_List_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Internal_List_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_LemmasExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Internal_List_Associative(builtin);
}
#ifdef __cplusplus
}
#endif
