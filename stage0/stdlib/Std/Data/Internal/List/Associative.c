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
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_inst_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_inst_56_);
return v_head_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x21(lean_object* v_00_u03b1_68_, lean_object* v_00_u03b2_69_, lean_object* v_inst_70_, lean_object* v_a_71_, lean_object* v_inst_72_, lean_object* v_x_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Std_Internal_List_getEntry_x21___redArg(v_inst_70_, v_a_71_, v_inst_72_, v_x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_h__2_77_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_apply_1(v_h__1_76_, v___x_78_);
return v___x_79_;
}
else
{
lean_object* v_head_80_; lean_object* v_tail_81_; lean_object* v_fst_82_; lean_object* v_snd_83_; lean_object* v___x_84_; 
lean_dec(v_h__1_76_);
v_head_80_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_head_80_);
v_tail_81_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_tail_81_);
lean_dec_ref(v_x_75_);
v_fst_82_ = lean_ctor_get(v_head_80_, 0);
lean_inc(v_fst_82_);
v_snd_83_ = lean_ctor_get(v_head_80_, 1);
lean_inc(v_snd_83_);
lean_dec(v_head_80_);
v___x_84_ = lean_apply_3(v_h__2_77_, v_fst_82_, v_snd_83_, v_tail_81_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_motive_87_, lean_object* v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_h__2_90_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_h__1_89_, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v_head_93_; lean_object* v_tail_94_; lean_object* v_fst_95_; lean_object* v_snd_96_; lean_object* v___x_97_; 
lean_dec(v_h__1_89_);
v_head_93_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_head_93_);
v_tail_94_ = lean_ctor_get(v_x_88_, 1);
lean_inc(v_tail_94_);
lean_dec_ref(v_x_88_);
v_fst_95_ = lean_ctor_get(v_head_93_, 0);
lean_inc(v_fst_95_);
v_snd_96_ = lean_ctor_get(v_head_93_, 1);
lean_inc(v_snd_96_);
lean_dec(v_head_93_);
v___x_97_ = lean_apply_3(v_h__2_90_, v_fst_95_, v_snd_96_, v_tail_94_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___redArg(lean_object* v_x_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v_h__2_100_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_apply_1(v_h__1_99_, v___x_101_);
return v___x_102_;
}
else
{
lean_object* v_head_103_; lean_object* v_tail_104_; lean_object* v_fst_105_; lean_object* v_snd_106_; lean_object* v___x_107_; 
lean_dec(v_h__1_99_);
v_head_103_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_head_103_);
v_tail_104_ = lean_ctor_get(v_x_98_, 1);
lean_inc(v_tail_104_);
lean_dec_ref(v_x_98_);
v_fst_105_ = lean_ctor_get(v_head_103_, 0);
lean_inc(v_fst_105_);
v_snd_106_ = lean_ctor_get(v_head_103_, 1);
lean_inc(v_snd_106_);
lean_dec(v_head_103_);
v___x_107_ = lean_apply_3(v_h__2_100_, v_fst_105_, v_snd_106_, v_tail_104_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_motive_110_, lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
if (lean_obj_tag(v_x_111_) == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_h__2_113_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_apply_1(v_h__1_112_, v___x_114_);
return v___x_115_;
}
else
{
lean_object* v_head_116_; lean_object* v_tail_117_; lean_object* v_fst_118_; lean_object* v_snd_119_; lean_object* v___x_120_; 
lean_dec(v_h__1_112_);
v_head_116_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_head_116_);
v_tail_117_ = lean_ctor_get(v_x_111_, 1);
lean_inc(v_tail_117_);
lean_dec_ref(v_x_111_);
v_fst_118_ = lean_ctor_get(v_head_116_, 0);
lean_inc(v_fst_118_);
v_snd_119_ = lean_ctor_get(v_head_116_, 1);
lean_inc(v_snd_119_);
lean_dec(v_head_116_);
v___x_120_ = lean_apply_3(v_h__2_113_, v_fst_118_, v_snd_119_, v_tail_117_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter___redArg(lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v_h__2_123_);
v___x_124_ = lean_box(0);
v___x_125_ = lean_apply_1(v_h__1_122_, v___x_124_);
return v___x_125_;
}
else
{
lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v_fst_128_; lean_object* v_snd_129_; lean_object* v___x_130_; 
lean_dec(v_h__1_122_);
v_head_126_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_head_126_);
v_tail_127_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_tail_127_);
lean_dec_ref(v_x_121_);
v_fst_128_ = lean_ctor_get(v_head_126_, 0);
lean_inc(v_fst_128_);
v_snd_129_ = lean_ctor_get(v_head_126_, 1);
lean_inc(v_snd_129_);
lean_dec(v_head_126_);
v___x_130_ = lean_apply_3(v_h__2_123_, v_fst_128_, v_snd_129_, v_tail_127_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter(lean_object* v_00_u03b1_131_, lean_object* v_00_u03b2_132_, lean_object* v_motive_133_, lean_object* v_x_134_, lean_object* v_h__1_135_, lean_object* v_h__2_136_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_h__2_136_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_1(v_h__1_135_, v___x_137_);
return v___x_138_;
}
else
{
lean_object* v_head_139_; lean_object* v_tail_140_; lean_object* v_fst_141_; lean_object* v_snd_142_; lean_object* v___x_143_; 
lean_dec(v_h__1_135_);
v_head_139_ = lean_ctor_get(v_x_134_, 0);
lean_inc(v_head_139_);
v_tail_140_ = lean_ctor_get(v_x_134_, 1);
lean_inc(v_tail_140_);
lean_dec_ref(v_x_134_);
v_fst_141_ = lean_ctor_get(v_head_139_, 0);
lean_inc(v_fst_141_);
v_snd_142_ = lean_ctor_get(v_head_139_, 1);
lean_inc(v_snd_142_);
lean_dec(v_head_139_);
v___x_143_ = lean_apply_3(v_h__2_136_, v_fst_141_, v_snd_142_, v_tail_140_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f___redArg(lean_object* v_inst_144_, lean_object* v_a_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v___x_147_; 
lean_dec(v_a_145_);
lean_dec_ref(v_inst_144_);
v___x_147_ = lean_box(0);
return v___x_147_;
}
else
{
lean_object* v_head_148_; lean_object* v_tail_149_; lean_object* v_fst_150_; lean_object* v_snd_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v_head_148_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_head_148_);
v_tail_149_ = lean_ctor_get(v_x_146_, 1);
lean_inc(v_tail_149_);
lean_dec_ref(v_x_146_);
v_fst_150_ = lean_ctor_get(v_head_148_, 0);
lean_inc(v_fst_150_);
v_snd_151_ = lean_ctor_get(v_head_148_, 1);
lean_inc(v_snd_151_);
lean_dec(v_head_148_);
lean_inc_ref(v_inst_144_);
lean_inc(v_a_145_);
v___x_152_ = lean_apply_2(v_inst_144_, v_fst_150_, v_a_145_);
v___x_153_ = lean_unbox(v___x_152_);
if (v___x_153_ == 0)
{
lean_dec(v_snd_151_);
v_x_146_ = v_tail_149_;
goto _start;
}
else
{
lean_object* v___x_155_; 
lean_dec(v_tail_149_);
lean_dec(v_a_145_);
lean_dec_ref(v_inst_144_);
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v_snd_151_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_inst_158_, lean_object* v_a_159_, lean_object* v_x_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_158_, v_a_159_, v_x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___redArg(lean_object* v_x_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_h__2_164_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_apply_1(v_h__1_163_, v___x_165_);
return v___x_166_;
}
else
{
lean_object* v_head_167_; lean_object* v_tail_168_; lean_object* v_fst_169_; lean_object* v_snd_170_; lean_object* v___x_171_; 
lean_dec(v_h__1_163_);
v_head_167_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_head_167_);
v_tail_168_ = lean_ctor_get(v_x_162_, 1);
lean_inc(v_tail_168_);
lean_dec_ref(v_x_162_);
v_fst_169_ = lean_ctor_get(v_head_167_, 0);
lean_inc(v_fst_169_);
v_snd_170_ = lean_ctor_get(v_head_167_, 1);
lean_inc(v_snd_170_);
lean_dec(v_head_167_);
v___x_171_ = lean_apply_3(v_h__2_164_, v_fst_169_, v_snd_170_, v_tail_168_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter(lean_object* v_00_u03b1_172_, lean_object* v_00_u03b2_173_, lean_object* v_motive_174_, lean_object* v_x_175_, lean_object* v_h__1_176_, lean_object* v_h__2_177_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_h__2_177_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_apply_1(v_h__1_176_, v___x_178_);
return v___x_179_;
}
else
{
lean_object* v_head_180_; lean_object* v_tail_181_; lean_object* v_fst_182_; lean_object* v_snd_183_; lean_object* v___x_184_; 
lean_dec(v_h__1_176_);
v_head_180_ = lean_ctor_get(v_x_175_, 0);
lean_inc(v_head_180_);
v_tail_181_ = lean_ctor_get(v_x_175_, 1);
lean_inc(v_tail_181_);
lean_dec_ref(v_x_175_);
v_fst_182_ = lean_ctor_get(v_head_180_, 0);
lean_inc(v_fst_182_);
v_snd_183_ = lean_ctor_get(v_head_180_, 1);
lean_inc(v_snd_183_);
lean_dec(v_head_180_);
v___x_184_ = lean_apply_3(v_h__2_177_, v_fst_182_, v_snd_183_, v_tail_181_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f___redArg(lean_object* v_inst_185_, lean_object* v_a_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v___x_188_; 
lean_dec(v_a_186_);
lean_dec_ref(v_inst_185_);
v___x_188_ = lean_box(0);
return v___x_188_;
}
else
{
lean_object* v_head_189_; lean_object* v_tail_190_; lean_object* v_fst_191_; lean_object* v_snd_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_head_189_ = lean_ctor_get(v_x_187_, 0);
lean_inc(v_head_189_);
v_tail_190_ = lean_ctor_get(v_x_187_, 1);
lean_inc(v_tail_190_);
lean_dec_ref(v_x_187_);
v_fst_191_ = lean_ctor_get(v_head_189_, 0);
lean_inc(v_fst_191_);
v_snd_192_ = lean_ctor_get(v_head_189_, 1);
lean_inc(v_snd_192_);
lean_dec(v_head_189_);
lean_inc_ref(v_inst_185_);
lean_inc(v_a_186_);
v___x_193_ = lean_apply_2(v_inst_185_, v_fst_191_, v_a_186_);
v___x_194_ = lean_unbox(v___x_193_);
if (v___x_194_ == 0)
{
lean_dec(v_snd_192_);
v_x_187_ = v_tail_190_;
goto _start;
}
else
{
lean_object* v___x_196_; 
lean_dec(v_tail_190_);
lean_dec(v_a_186_);
lean_dec_ref(v_inst_185_);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v_snd_192_);
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f(lean_object* v_00_u03b1_197_, lean_object* v_00_u03b2_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_199_, v_a_201_, v_x_202_);
return v___x_203_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg___lam__0(lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_l_u2082_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_fst_208_; lean_object* v_snd_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_fst_208_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_fst_208_);
v_snd_209_ = lean_ctor_get(v_x_207_, 1);
lean_inc(v_snd_209_);
lean_dec_ref(v_x_207_);
lean_inc(v_fst_208_);
v___x_210_ = lean_apply_1(v_inst_204_, v_fst_208_);
v___x_211_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_205_, v_fst_208_, v_l_u2082_206_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v_snd_209_);
v___x_213_ = l_Option_instBEq_beq___redArg(v___x_210_, v___x_211_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___lam__0___boxed(lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_l_u2082_216_, lean_object* v_x_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Std_Internal_List_beqModel___redArg___lam__0(v_inst_214_, v_inst_215_, v_l_u2082_216_, v_x_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg(lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_l_u2081_222_, lean_object* v_l_u2082_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = l_List_lengthTR___redArg(v_l_u2081_222_);
v___x_225_ = l_List_lengthTR___redArg(v_l_u2082_223_);
v___x_226_ = lean_nat_dec_eq(v___x_224_, v___x_225_);
lean_dec(v___x_225_);
lean_dec(v___x_224_);
if (v___x_226_ == 0)
{
lean_dec(v_l_u2082_223_);
lean_dec(v_l_u2081_222_);
lean_dec_ref(v_inst_221_);
lean_dec_ref(v_inst_220_);
return v___x_226_;
}
else
{
lean_object* v___f_227_; uint8_t v___x_228_; 
v___f_227_ = lean_alloc_closure((void*)(l_Std_Internal_List_beqModel___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_227_, 0, v_inst_221_);
lean_closure_set(v___f_227_, 1, v_inst_220_);
lean_closure_set(v___f_227_, 2, v_l_u2082_223_);
v___x_228_ = l_List_all___redArg(v_l_u2081_222_, v___f_227_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___boxed(lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_l_u2081_231_, lean_object* v_l_u2082_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Std_Internal_List_beqModel___redArg(v_inst_229_, v_inst_230_, v_l_u2081_231_, v_l_u2082_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_l_u2081_240_, lean_object* v_l_u2082_241_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = l_Std_Internal_List_beqModel___redArg(v_inst_237_, v_inst_239_, v_l_u2081_240_, v_l_u2082_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___boxed(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_l_u2081_248_, lean_object* v_l_u2082_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Std_Internal_List_beqModel(v_00_u03b1_243_, v_00_u03b2_244_, v_inst_245_, v_inst_246_, v_inst_247_, v_l_u2081_248_, v_l_u2082_249_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter___redArg(lean_object* v_x_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_h__2_254_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_apply_1(v_h__1_253_, v___x_255_);
return v___x_256_;
}
else
{
lean_object* v_head_257_; lean_object* v_tail_258_; lean_object* v_fst_259_; lean_object* v_snd_260_; lean_object* v___x_261_; 
lean_dec(v_h__1_253_);
v_head_257_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_head_257_);
v_tail_258_ = lean_ctor_get(v_x_252_, 1);
lean_inc(v_tail_258_);
lean_dec_ref(v_x_252_);
v_fst_259_ = lean_ctor_get(v_head_257_, 0);
lean_inc(v_fst_259_);
v_snd_260_ = lean_ctor_get(v_head_257_, 1);
lean_inc(v_snd_260_);
lean_dec(v_head_257_);
v___x_261_ = lean_apply_3(v_h__2_254_, v_fst_259_, v_snd_260_, v_tail_258_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter(lean_object* v_00_u03b1_262_, lean_object* v_00_u03b2_263_, lean_object* v_motive_264_, lean_object* v_x_265_, lean_object* v_h__1_266_, lean_object* v_h__2_267_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_h__2_267_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_apply_1(v_h__1_266_, v___x_268_);
return v___x_269_;
}
else
{
lean_object* v_head_270_; lean_object* v_tail_271_; lean_object* v_fst_272_; lean_object* v_snd_273_; lean_object* v___x_274_; 
lean_dec(v_h__1_266_);
v_head_270_ = lean_ctor_get(v_x_265_, 0);
lean_inc(v_head_270_);
v_tail_271_ = lean_ctor_get(v_x_265_, 1);
lean_inc(v_tail_271_);
lean_dec_ref(v_x_265_);
v_fst_272_ = lean_ctor_get(v_head_270_, 0);
lean_inc(v_fst_272_);
v_snd_273_ = lean_ctor_get(v_head_270_, 1);
lean_inc(v_snd_273_);
lean_dec(v_head_270_);
v___x_274_ = lean_apply_3(v_h__2_267_, v_fst_272_, v_snd_273_, v_tail_271_);
return v___x_274_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg___lam__0(lean_object* v_inst_275_, lean_object* v_l_u2082_276_, lean_object* v_inst_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_fst_279_; lean_object* v_snd_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_fst_279_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_fst_279_);
v_snd_280_ = lean_ctor_get(v_x_278_, 1);
lean_inc(v_snd_280_);
lean_dec_ref(v_x_278_);
v___x_281_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_275_, v_fst_279_, v_l_u2082_276_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v_snd_280_);
v___x_283_ = l_Option_instBEq_beq___redArg(v_inst_277_, v___x_281_, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed(lean_object* v_inst_284_, lean_object* v_l_u2082_285_, lean_object* v_inst_286_, lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_Internal_List_Const_beqModel___redArg___lam__0(v_inst_284_, v_l_u2082_285_, v_inst_286_, v_x_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_l_u2081_292_, lean_object* v_l_u2082_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = l_List_lengthTR___redArg(v_l_u2081_292_);
v___x_295_ = l_List_lengthTR___redArg(v_l_u2082_293_);
v___x_296_ = lean_nat_dec_eq(v___x_294_, v___x_295_);
lean_dec(v___x_295_);
lean_dec(v___x_294_);
if (v___x_296_ == 0)
{
lean_dec(v_l_u2082_293_);
lean_dec(v_l_u2081_292_);
lean_dec_ref(v_inst_291_);
lean_dec_ref(v_inst_290_);
return v___x_296_;
}
else
{
lean_object* v___f_297_; uint8_t v___x_298_; 
v___f_297_ = lean_alloc_closure((void*)(l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_297_, 0, v_inst_290_);
lean_closure_set(v___f_297_, 1, v_l_u2082_293_);
lean_closure_set(v___f_297_, 2, v_inst_291_);
v___x_298_ = l_List_all___redArg(v_l_u2081_292_, v___f_297_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___boxed(lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_l_u2081_301_, lean_object* v_l_u2082_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_299_, v_inst_300_, v_l_u2081_301_, v_l_u2082_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel(lean_object* v_00_u03b1_305_, lean_object* v_00_u03b2_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_l_u2081_309_, lean_object* v_l_u2082_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_307_, v_inst_308_, v_l_u2081_309_, v_l_u2082_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___boxed(lean_object* v_00_u03b1_312_, lean_object* v_00_u03b2_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_l_u2081_316_, lean_object* v_l_u2082_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Std_Internal_List_Const_beqModel(v_00_u03b1_312_, v_00_u03b2_313_, v_inst_314_, v_inst_315_, v_l_u2081_316_, v_l_u2082_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
lean_object* v___x_322_; 
lean_dec(v_x_321_);
v___x_322_ = lean_box(0);
return v___x_322_;
}
else
{
lean_object* v_val_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
v_val_323_ = lean_ctor_get(v_x_320_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_320_);
if (v_isSharedCheck_331_ == 0)
{
v___x_325_ = v_x_320_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_val_323_);
lean_dec(v_x_320_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_apply_2(v_x_321_, v_val_323_, lean_box(0));
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_327_);
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap(lean_object* v_00_u03b1_332_, lean_object* v_00_u03b2_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(v_x_334_, v_x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___redArg(lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_h__1_339_, lean_object* v_h__2_340_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v___x_341_; 
lean_dec(v_h__2_340_);
v___x_341_ = lean_apply_1(v_h__1_339_, v_x_338_);
return v___x_341_;
}
else
{
lean_object* v_val_342_; lean_object* v___x_343_; 
lean_dec(v_h__1_339_);
v_val_342_ = lean_ctor_get(v_x_337_, 0);
lean_inc(v_val_342_);
lean_dec_ref(v_x_337_);
v___x_343_ = lean_apply_2(v_h__2_340_, v_val_342_, v_x_338_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_motive_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_h__1_349_, lean_object* v_h__2_350_){
_start:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v___x_351_; 
lean_dec(v_h__2_350_);
v___x_351_ = lean_apply_1(v_h__1_349_, v_x_348_);
return v___x_351_;
}
else
{
lean_object* v_val_352_; lean_object* v___x_353_; 
lean_dec(v_h__1_349_);
v_val_352_ = lean_ctor_get(v_x_347_, 0);
lean_inc(v_val_352_);
lean_dec_ref(v_x_347_);
v___x_353_ = lean_apply_2(v_h__2_350_, v_val_352_, v_x_348_);
return v___x_353_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey___redArg(lean_object* v_inst_354_, lean_object* v_a_355_, lean_object* v_x_356_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
uint8_t v___x_357_; 
lean_dec(v_a_355_);
lean_dec_ref(v_inst_354_);
v___x_357_ = 0;
return v___x_357_;
}
else
{
lean_object* v_head_358_; lean_object* v_tail_359_; lean_object* v_fst_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_head_358_ = lean_ctor_get(v_x_356_, 0);
lean_inc(v_head_358_);
v_tail_359_ = lean_ctor_get(v_x_356_, 1);
lean_inc(v_tail_359_);
lean_dec_ref(v_x_356_);
v_fst_360_ = lean_ctor_get(v_head_358_, 0);
lean_inc(v_fst_360_);
lean_dec(v_head_358_);
lean_inc_ref(v_inst_354_);
lean_inc(v_a_355_);
v___x_361_ = lean_apply_2(v_inst_354_, v_fst_360_, v_a_355_);
v___x_362_ = lean_unbox(v___x_361_);
if (v___x_362_ == 0)
{
v_x_356_ = v_tail_359_;
goto _start;
}
else
{
uint8_t v___x_364_; 
lean_dec(v_tail_359_);
lean_dec(v_a_355_);
lean_dec_ref(v_inst_354_);
v___x_364_ = lean_unbox(v___x_361_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___redArg___boxed(lean_object* v_inst_365_, lean_object* v_a_366_, lean_object* v_x_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Std_Internal_List_containsKey___redArg(v_inst_365_, v_a_366_, v_x_367_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_inst_372_, lean_object* v_a_373_, lean_object* v_x_374_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = l_Std_Internal_List_containsKey___redArg(v_inst_372_, v_a_373_, v_x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___boxed(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v_inst_378_, lean_object* v_a_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_Std_Internal_List_containsKey(v_00_u03b1_376_, v_00_u03b2_377_, v_inst_378_, v_a_379_, v_x_380_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry___redArg(lean_object* v_inst_383_, lean_object* v_a_384_, lean_object* v_l_385_){
_start:
{
lean_object* v___x_386_; lean_object* v_val_387_; 
v___x_386_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_383_, v_a_384_, v_l_385_);
v_val_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_val_387_);
lean_dec(v___x_386_);
return v_val_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_inst_390_, lean_object* v_a_391_, lean_object* v_l_392_, lean_object* v_h_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_Internal_List_getEntry___redArg(v_inst_390_, v_a_391_, v_l_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue___redArg(lean_object* v_inst_395_, lean_object* v_a_396_, lean_object* v_l_397_){
_start:
{
lean_object* v___x_398_; lean_object* v_val_399_; 
v___x_398_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_395_, v_a_396_, v_l_397_);
v_val_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_val_399_);
lean_dec(v___x_398_);
return v_val_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue(lean_object* v_00_u03b1_400_, lean_object* v_00_u03b2_401_, lean_object* v_inst_402_, lean_object* v_a_403_, lean_object* v_l_404_, lean_object* v_h_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_Internal_List_getValue___redArg(v_inst_402_, v_a_403_, v_l_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast___redArg(lean_object* v_inst_407_, lean_object* v_a_408_, lean_object* v_l_409_){
_start:
{
lean_object* v___x_410_; lean_object* v_val_411_; 
v___x_410_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_407_, v_a_408_, v_l_409_);
v_val_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_val_411_);
lean_dec(v___x_410_);
return v_val_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_a_416_, lean_object* v_l_417_, lean_object* v_h_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_Internal_List_getValueCast___redArg(v_inst_414_, v_a_416_, v_l_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg(lean_object* v_inst_420_, lean_object* v_a_421_, lean_object* v_l_422_, lean_object* v_fallback_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_420_, v_a_421_, v_l_422_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_inc(v_fallback_423_);
return v_fallback_423_;
}
else
{
lean_object* v_val_425_; 
v_val_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_val_425_);
lean_dec_ref(v___x_424_);
return v_val_425_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg___boxed(lean_object* v_inst_426_, lean_object* v_a_427_, lean_object* v_l_428_, lean_object* v_fallback_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_Internal_List_getValueCastD___redArg(v_inst_426_, v_a_427_, v_l_428_, v_fallback_429_);
lean_dec(v_fallback_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD(lean_object* v_00_u03b1_431_, lean_object* v_00_u03b2_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_a_435_, lean_object* v_l_436_, lean_object* v_fallback_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Std_Internal_List_getValueCastD___redArg(v_inst_433_, v_a_435_, v_l_436_, v_fallback_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___boxed(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_a_443_, lean_object* v_l_444_, lean_object* v_fallback_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Internal_List_getValueCastD(v_00_u03b1_439_, v_00_u03b2_440_, v_inst_441_, v_inst_442_, v_a_443_, v_l_444_, v_fallback_445_);
lean_dec(v_fallback_445_);
return v_res_446_;
}
}
static lean_object* _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_450_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__2));
v___x_451_ = lean_unsigned_to_nat(14u);
v___x_452_ = lean_unsigned_to_nat(22u);
v___x_453_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__1));
v___x_454_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__0));
v___x_455_ = l_mkPanicMessageWithDecl(v___x_454_, v___x_453_, v___x_452_, v___x_451_, v___x_450_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___redArg(lean_object* v_inst_456_, lean_object* v_a_457_, lean_object* v_inst_458_, lean_object* v_l_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_456_, v_a_457_, v_l_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_462_ = l_panic___redArg(v_inst_458_, v___x_461_);
return v___x_462_;
}
else
{
lean_object* v_val_463_; 
lean_dec(v_inst_458_);
v_val_463_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_val_463_);
lean_dec_ref(v___x_460_);
return v_val_463_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_a_468_, lean_object* v_inst_469_, lean_object* v_l_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_Internal_List_getValueCast_x21___redArg(v_inst_466_, v_a_468_, v_inst_469_, v_l_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg(lean_object* v_inst_472_, lean_object* v_a_473_, lean_object* v_l_474_, lean_object* v_fallback_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_472_, v_a_473_, v_l_474_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_inc(v_fallback_475_);
return v_fallback_475_;
}
else
{
lean_object* v_val_477_; 
v_val_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_val_477_);
lean_dec_ref(v___x_476_);
return v_val_477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg___boxed(lean_object* v_inst_478_, lean_object* v_a_479_, lean_object* v_l_480_, lean_object* v_fallback_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Internal_List_getValueD___redArg(v_inst_478_, v_a_479_, v_l_480_, v_fallback_481_);
lean_dec(v_fallback_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_inst_485_, lean_object* v_a_486_, lean_object* v_l_487_, lean_object* v_fallback_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_Internal_List_getValueD___redArg(v_inst_485_, v_a_486_, v_l_487_, v_fallback_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___boxed(lean_object* v_00_u03b1_490_, lean_object* v_00_u03b2_491_, lean_object* v_inst_492_, lean_object* v_a_493_, lean_object* v_l_494_, lean_object* v_fallback_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_Internal_List_getValueD(v_00_u03b1_490_, v_00_u03b2_491_, v_inst_492_, v_a_493_, v_l_494_, v_fallback_495_);
lean_dec(v_fallback_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg(lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_a_499_, lean_object* v_l_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_497_, v_a_499_, v_l_500_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_503_ = l_panic___redArg(v_inst_498_, v___x_502_);
return v___x_503_;
}
else
{
lean_object* v_val_504_; 
lean_dec(v_inst_498_);
v_val_504_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_val_504_);
lean_dec_ref(v___x_501_);
return v_val_504_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21(lean_object* v_00_u03b1_505_, lean_object* v_00_u03b2_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_a_509_, lean_object* v_l_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_Internal_List_getValue_x21___redArg(v_inst_507_, v_inst_508_, v_a_509_, v_l_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f___redArg(lean_object* v_inst_512_, lean_object* v_a_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v___x_515_; 
lean_dec(v_a_513_);
lean_dec_ref(v_inst_512_);
v___x_515_ = lean_box(0);
return v___x_515_;
}
else
{
lean_object* v_head_516_; lean_object* v_tail_517_; lean_object* v_fst_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_head_516_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_head_516_);
v_tail_517_ = lean_ctor_get(v_x_514_, 1);
lean_inc(v_tail_517_);
lean_dec_ref(v_x_514_);
v_fst_518_ = lean_ctor_get(v_head_516_, 0);
lean_inc(v_fst_518_);
lean_dec(v_head_516_);
lean_inc_ref(v_inst_512_);
lean_inc(v_a_513_);
lean_inc(v_fst_518_);
v___x_519_ = lean_apply_2(v_inst_512_, v_fst_518_, v_a_513_);
v___x_520_ = lean_unbox(v___x_519_);
if (v___x_520_ == 0)
{
lean_dec(v_fst_518_);
v_x_514_ = v_tail_517_;
goto _start;
}
else
{
lean_object* v___x_522_; 
lean_dec(v_tail_517_);
lean_dec(v_a_513_);
lean_dec_ref(v_inst_512_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v_fst_518_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f(lean_object* v_00_u03b1_523_, lean_object* v_00_u03b2_524_, lean_object* v_inst_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_525_, v_a_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey___redArg(lean_object* v_inst_529_, lean_object* v_a_530_, lean_object* v_l_531_){
_start:
{
lean_object* v___x_532_; lean_object* v_val_533_; 
v___x_532_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_529_, v_a_530_, v_l_531_);
v_val_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_val_533_);
lean_dec(v___x_532_);
return v_val_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey(lean_object* v_00_u03b1_534_, lean_object* v_00_u03b2_535_, lean_object* v_inst_536_, lean_object* v_a_537_, lean_object* v_l_538_, lean_object* v_h_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_Internal_List_getKey___redArg(v_inst_536_, v_a_537_, v_l_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg(lean_object* v_inst_541_, lean_object* v_a_542_, lean_object* v_l_543_, lean_object* v_fallback_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_541_, v_a_542_, v_l_543_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_inc(v_fallback_544_);
return v_fallback_544_;
}
else
{
lean_object* v_val_546_; 
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref(v___x_545_);
return v_val_546_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg___boxed(lean_object* v_inst_547_, lean_object* v_a_548_, lean_object* v_l_549_, lean_object* v_fallback_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_Internal_List_getKeyD___redArg(v_inst_547_, v_a_548_, v_l_549_, v_fallback_550_);
lean_dec(v_fallback_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD(lean_object* v_00_u03b1_552_, lean_object* v_00_u03b2_553_, lean_object* v_inst_554_, lean_object* v_a_555_, lean_object* v_l_556_, lean_object* v_fallback_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_Internal_List_getKeyD___redArg(v_inst_554_, v_a_555_, v_l_556_, v_fallback_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___boxed(lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_, lean_object* v_inst_561_, lean_object* v_a_562_, lean_object* v_l_563_, lean_object* v_fallback_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_Internal_List_getKeyD(v_00_u03b1_559_, v_00_u03b2_560_, v_inst_561_, v_a_562_, v_l_563_, v_fallback_564_);
lean_dec(v_fallback_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg(lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_a_568_, lean_object* v_l_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_566_, v_a_568_, v_l_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_572_ = l_panic___redArg(v_inst_567_, v___x_571_);
return v___x_572_;
}
else
{
lean_object* v_val_573_; 
lean_dec(v_inst_567_);
v_val_573_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_val_573_);
lean_dec_ref(v___x_570_);
return v_val_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21(lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_a_578_, lean_object* v_l_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_Internal_List_getKey_x21___redArg(v_inst_576_, v_inst_577_, v_a_578_, v_l_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry___redArg(lean_object* v_inst_581_, lean_object* v_k_582_, lean_object* v_v_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v___x_585_; 
lean_dec(v_v_583_);
lean_dec(v_k_582_);
lean_dec_ref(v_inst_581_);
v___x_585_ = lean_box(0);
return v___x_585_;
}
else
{
lean_object* v_head_586_; lean_object* v_tail_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_610_; 
v_head_586_ = lean_ctor_get(v_x_584_, 0);
v_tail_587_ = lean_ctor_get(v_x_584_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_610_ == 0)
{
v___x_589_ = v_x_584_;
v_isShared_590_ = v_isSharedCheck_610_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_tail_587_);
lean_inc(v_head_586_);
lean_dec(v_x_584_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_610_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_fst_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_fst_591_ = lean_ctor_get(v_head_586_, 0);
lean_inc_ref(v_inst_581_);
lean_inc(v_k_582_);
lean_inc(v_fst_591_);
v___x_592_ = lean_apply_2(v_inst_581_, v_fst_591_, v_k_582_);
v___x_593_ = lean_unbox(v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_581_, v_k_582_, v_v_583_, v_tail_587_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___x_594_);
v___x_596_ = v___x_589_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_head_586_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
else
{
lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref(v_inst_581_);
v_isSharedCheck_607_ = !lean_is_exclusive(v_head_586_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; lean_object* v_unused_609_; 
v_unused_608_ = lean_ctor_get(v_head_586_, 1);
lean_dec(v_unused_608_);
v_unused_609_ = lean_ctor_get(v_head_586_, 0);
lean_dec(v_unused_609_);
v___x_599_ = v_head_586_;
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
else
{
lean_dec(v_head_586_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v_v_583_);
lean_ctor_set(v___x_599_, 0, v_k_582_);
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_k_582_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_v_583_);
v___x_602_ = v_reuseFailAlloc_606_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_604_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_602_);
v___x_604_ = v___x_589_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_tail_587_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry(lean_object* v_00_u03b1_611_, lean_object* v_00_u03b2_612_, lean_object* v_inst_613_, lean_object* v_k_614_, lean_object* v_v_615_, lean_object* v_x_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_613_, v_k_614_, v_v_615_, v_x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey___redArg(lean_object* v_inst_618_, lean_object* v_k_619_, lean_object* v_x_620_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_object* v___x_621_; 
lean_dec(v_k_619_);
lean_dec_ref(v_inst_618_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_634_; 
v_head_622_ = lean_ctor_get(v_x_620_, 0);
v_tail_623_ = lean_ctor_get(v_x_620_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_634_ == 0)
{
v___x_625_ = v_x_620_;
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_tail_623_);
lean_inc(v_head_622_);
lean_dec(v_x_620_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_fst_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_fst_627_ = lean_ctor_get(v_head_622_, 0);
lean_inc_ref(v_inst_618_);
lean_inc(v_k_619_);
lean_inc(v_fst_627_);
v___x_628_ = lean_apply_2(v_inst_618_, v_fst_627_, v_k_619_);
v___x_629_ = lean_unbox(v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = l_Std_Internal_List_eraseKey___redArg(v_inst_618_, v_k_619_, v_tail_623_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_630_);
v___x_632_ = v___x_625_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_head_622_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
lean_del_object(v___x_625_);
lean_dec(v_head_622_);
lean_dec(v_k_619_);
lean_dec_ref(v_inst_618_);
return v_tail_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey(lean_object* v_00_u03b1_635_, lean_object* v_00_u03b2_636_, lean_object* v_inst_637_, lean_object* v_k_638_, lean_object* v_x_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_Internal_List_eraseKey___redArg(v_inst_637_, v_k_638_, v_x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry___redArg(lean_object* v_inst_641_, lean_object* v_k_642_, lean_object* v_v_643_, lean_object* v_l_644_){
_start:
{
uint8_t v___x_645_; 
lean_inc(v_l_644_);
lean_inc(v_k_642_);
lean_inc_ref(v_inst_641_);
v___x_645_ = l_Std_Internal_List_containsKey___redArg(v_inst_641_, v_k_642_, v_l_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec_ref(v_inst_641_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v_k_642_);
lean_ctor_set(v___x_646_, 1, v_v_643_);
v___x_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v_l_644_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_641_, v_k_642_, v_v_643_, v_l_644_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_inst_651_, lean_object* v_k_652_, lean_object* v_v_653_, lean_object* v_l_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_Internal_List_insertEntry___redArg(v_inst_651_, v_k_652_, v_v_653_, v_l_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew___redArg(lean_object* v_inst_656_, lean_object* v_k_657_, lean_object* v_v_658_, lean_object* v_l_659_){
_start:
{
uint8_t v___x_660_; 
lean_inc(v_l_659_);
lean_inc(v_k_657_);
v___x_660_ = l_Std_Internal_List_containsKey___redArg(v_inst_656_, v_k_657_, v_l_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_k_657_);
lean_ctor_set(v___x_661_, 1, v_v_658_);
v___x_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v_l_659_);
return v___x_662_;
}
else
{
lean_dec(v_v_658_);
lean_dec(v_k_657_);
return v_l_659_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew(lean_object* v_00_u03b1_663_, lean_object* v_00_u03b2_664_, lean_object* v_inst_665_, lean_object* v_k_666_, lean_object* v_v_667_, lean_object* v_l_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_665_, v_k_666_, v_v_667_, v_l_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_670_, lean_object* v_h__1_671_, lean_object* v_h__2_672_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v_h__2_672_);
v___x_673_ = lean_box(0);
v___x_674_ = lean_apply_1(v_h__1_671_, v___x_673_);
return v___x_674_;
}
else
{
lean_object* v_val_675_; lean_object* v___x_676_; 
lean_dec(v_h__1_671_);
v_val_675_ = lean_ctor_get(v_x_670_, 0);
lean_inc(v_val_675_);
lean_dec_ref(v_x_670_);
v___x_676_ = lean_apply_1(v_h__2_672_, v_val_675_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_677_, lean_object* v_motive_678_, lean_object* v_x_679_, lean_object* v_h__1_680_, lean_object* v_h__2_681_){
_start:
{
if (lean_obj_tag(v_x_679_) == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_h__2_681_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_apply_1(v_h__1_680_, v___x_682_);
return v___x_683_;
}
else
{
lean_object* v_val_684_; lean_object* v___x_685_; 
lean_dec(v_h__1_680_);
v_val_684_ = lean_ctor_get(v_x_679_, 0);
lean_inc(v_val_684_);
lean_dec_ref(v_x_679_);
v___x_685_ = lean_apply_1(v_h__2_681_, v_val_684_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_686_, lean_object* v_h__1_687_, lean_object* v_h__2_688_){
_start:
{
if (lean_obj_tag(v_x_686_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; 
lean_dec(v_h__2_688_);
v_a_689_ = lean_ctor_get(v_x_686_, 0);
lean_inc(v_a_689_);
lean_dec_ref(v_x_686_);
v___x_690_ = lean_apply_1(v_h__1_687_, v_a_689_);
return v___x_690_;
}
else
{
lean_object* v_a_691_; lean_object* v___x_692_; 
lean_dec(v_h__1_687_);
v_a_691_ = lean_ctor_get(v_x_686_, 0);
lean_inc(v_a_691_);
lean_dec_ref(v_x_686_);
v___x_692_ = lean_apply_1(v_h__2_688_, v_a_691_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_693_, lean_object* v_motive_694_, lean_object* v_x_695_, lean_object* v_h__1_696_, lean_object* v_h__2_697_){
_start:
{
if (lean_obj_tag(v_x_695_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; 
lean_dec(v_h__2_697_);
v_a_698_ = lean_ctor_get(v_x_695_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v_x_695_);
v___x_699_ = lean_apply_1(v_h__1_696_, v_a_698_);
return v___x_699_;
}
else
{
lean_object* v_a_700_; lean_object* v___x_701_; 
lean_dec(v_h__1_696_);
v_a_700_ = lean_ctor_get(v_x_695_, 0);
lean_inc(v_a_700_);
lean_dec_ref(v_x_695_);
v___x_701_ = lean_apply_1(v_h__2_697_, v_a_700_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList___redArg(lean_object* v_inst_702_, lean_object* v_l_703_, lean_object* v_toInsert_704_){
_start:
{
if (lean_obj_tag(v_toInsert_704_) == 0)
{
lean_dec_ref(v_inst_702_);
return v_l_703_;
}
else
{
lean_object* v_head_705_; lean_object* v_tail_706_; lean_object* v_fst_707_; lean_object* v_snd_708_; lean_object* v___x_709_; 
v_head_705_ = lean_ctor_get(v_toInsert_704_, 0);
lean_inc(v_head_705_);
v_tail_706_ = lean_ctor_get(v_toInsert_704_, 1);
lean_inc(v_tail_706_);
lean_dec_ref(v_toInsert_704_);
v_fst_707_ = lean_ctor_get(v_head_705_, 0);
lean_inc(v_fst_707_);
v_snd_708_ = lean_ctor_get(v_head_705_, 1);
lean_inc(v_snd_708_);
lean_dec(v_head_705_);
lean_inc_ref(v_inst_702_);
v___x_709_ = l_Std_Internal_List_insertEntry___redArg(v_inst_702_, v_fst_707_, v_snd_708_, v_l_703_);
v_l_703_ = v___x_709_;
v_toInsert_704_ = v_tail_706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList(lean_object* v_00_u03b1_711_, lean_object* v_00_u03b2_712_, lean_object* v_inst_713_, lean_object* v_l_714_, lean_object* v_toInsert_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_Internal_List_insertList___redArg(v_inst_713_, v_l_714_, v_toInsert_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew___redArg(lean_object* v_inst_717_, lean_object* v_l_718_, lean_object* v_toInsert_719_){
_start:
{
if (lean_obj_tag(v_toInsert_719_) == 0)
{
lean_dec_ref(v_inst_717_);
return v_l_718_;
}
else
{
lean_object* v_head_720_; lean_object* v_tail_721_; lean_object* v_fst_722_; lean_object* v_snd_723_; lean_object* v___x_724_; 
v_head_720_ = lean_ctor_get(v_toInsert_719_, 0);
lean_inc(v_head_720_);
v_tail_721_ = lean_ctor_get(v_toInsert_719_, 1);
lean_inc(v_tail_721_);
lean_dec_ref(v_toInsert_719_);
v_fst_722_ = lean_ctor_get(v_head_720_, 0);
lean_inc(v_fst_722_);
v_snd_723_ = lean_ctor_get(v_head_720_, 1);
lean_inc(v_snd_723_);
lean_dec(v_head_720_);
lean_inc_ref(v_inst_717_);
v___x_724_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_717_, v_fst_722_, v_snd_723_, v_l_718_);
v_l_718_ = v___x_724_;
v_toInsert_719_ = v_tail_721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew(lean_object* v_00_u03b1_726_, lean_object* v_00_u03b2_727_, lean_object* v_inst_728_, lean_object* v_l_729_, lean_object* v_toInsert_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_Internal_List_insertListIfNew___redArg(v_inst_728_, v_l_729_, v_toInsert_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList___redArg(lean_object* v_inst_732_, lean_object* v_l_u2081_733_, lean_object* v_l_u2082_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = l_List_lengthTR___redArg(v_l_u2081_733_);
v___x_736_ = l_List_lengthTR___redArg(v_l_u2082_734_);
v___x_737_ = lean_nat_dec_le(v___x_735_, v___x_736_);
lean_dec(v___x_736_);
lean_dec(v___x_735_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_Internal_List_insertList___redArg(v_inst_732_, v_l_u2081_733_, v_l_u2082_734_);
return v___x_738_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = l_Std_Internal_List_insertListIfNew___redArg(v_inst_732_, v_l_u2082_734_, v_l_u2081_733_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList(lean_object* v_00_u03b1_740_, lean_object* v_00_u03b2_741_, lean_object* v_inst_742_, lean_object* v_l_u2081_743_, lean_object* v_l_u2082_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Std_Internal_List_insertSmallerList___redArg(v_inst_742_, v_l_u2081_743_, v_l_u2082_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma___redArg(lean_object* v_p_746_){
_start:
{
lean_object* v_fst_747_; lean_object* v_snd_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
v_fst_747_ = lean_ctor_get(v_p_746_, 0);
v_snd_748_ = lean_ctor_get(v_p_746_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_p_746_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v_p_746_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_snd_748_);
lean_inc(v_fst_747_);
lean_dec(v_p_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_fst_747_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_snd_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_p_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Std_Internal_List_Prod_toSigma___redArg(v_p_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst___redArg(lean_object* v_inst_761_, lean_object* v_l_762_, lean_object* v_toInsert_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_764_ = ((lean_object*)(l_Std_Internal_List_insertListConst___redArg___closed__0));
v___x_765_ = lean_box(0);
v___x_766_ = l_List_mapTR_loop___redArg(v___x_764_, v_toInsert_763_, v___x_765_);
v___x_767_ = l_Std_Internal_List_insertList___redArg(v_inst_761_, v_l_762_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst(lean_object* v_00_u03b1_768_, lean_object* v_00_u03b2_769_, lean_object* v_inst_770_, lean_object* v_l_771_, lean_object* v_toInsert_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_Internal_List_insertListConst___redArg(v_inst_770_, v_l_771_, v_toInsert_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit___redArg(lean_object* v_inst_774_, lean_object* v_l_775_, lean_object* v_toInsert_776_){
_start:
{
if (lean_obj_tag(v_toInsert_776_) == 0)
{
lean_dec_ref(v_inst_774_);
return v_l_775_;
}
else
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_head_777_ = lean_ctor_get(v_toInsert_776_, 0);
lean_inc(v_head_777_);
v_tail_778_ = lean_ctor_get(v_toInsert_776_, 1);
lean_inc(v_tail_778_);
lean_dec_ref(v_toInsert_776_);
v___x_779_ = lean_box(0);
lean_inc_ref(v_inst_774_);
v___x_780_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_774_, v_head_777_, v___x_779_, v_l_775_);
v_l_775_ = v___x_780_;
v_toInsert_776_ = v_tail_778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit(lean_object* v_00_u03b1_782_, lean_object* v_inst_783_, lean_object* v_l_784_, lean_object* v_toInsert_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_Internal_List_insertListIfNewUnit___redArg(v_inst_783_, v_l_784_, v_toInsert_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(lean_object* v_toInsert_787_, lean_object* v_h__1_788_, lean_object* v_h__2_789_){
_start:
{
if (lean_obj_tag(v_toInsert_787_) == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec(v_h__2_789_);
v___x_790_ = lean_box(0);
v___x_791_ = lean_apply_1(v_h__1_788_, v___x_790_);
return v___x_791_;
}
else
{
lean_object* v_head_792_; lean_object* v_tail_793_; lean_object* v___x_794_; 
lean_dec(v_h__1_788_);
v_head_792_ = lean_ctor_get(v_toInsert_787_, 0);
lean_inc(v_head_792_);
v_tail_793_ = lean_ctor_get(v_toInsert_787_, 1);
lean_inc(v_tail_793_);
lean_dec_ref(v_toInsert_787_);
v___x_794_ = lean_apply_2(v_h__2_789_, v_head_792_, v_tail_793_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object* v_00_u03b1_795_, lean_object* v_motive_796_, lean_object* v_toInsert_797_, lean_object* v_h__1_798_, lean_object* v_h__2_799_){
_start:
{
if (lean_obj_tag(v_toInsert_797_) == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v_h__2_799_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_apply_1(v_h__1_798_, v___x_800_);
return v___x_801_;
}
else
{
lean_object* v_head_802_; lean_object* v_tail_803_; lean_object* v___x_804_; 
lean_dec(v_h__1_798_);
v_head_802_ = lean_ctor_get(v_toInsert_797_, 0);
lean_inc(v_head_802_);
v_tail_803_ = lean_ctor_get(v_toInsert_797_, 1);
lean_inc(v_tail_803_);
lean_dec_ref(v_toInsert_797_);
v___x_804_ = lean_apply_2(v_h__2_799_, v_head_802_, v_tail_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey___redArg(lean_object* v_inst_805_, lean_object* v_k_806_, lean_object* v_f_807_, lean_object* v_l_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc(v_l_808_);
lean_inc(v_k_806_);
lean_inc_ref(v_inst_805_);
v___x_809_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_805_, v_k_806_, v_l_808_);
v___x_810_ = lean_apply_1(v_f_807_, v___x_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_Internal_List_eraseKey___redArg(v_inst_805_, v_k_806_, v_l_808_);
return v___x_811_;
}
else
{
lean_object* v_val_812_; lean_object* v___x_813_; 
v_val_812_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_val_812_);
lean_dec_ref(v___x_810_);
v___x_813_ = l_Std_Internal_List_insertEntry___redArg(v_inst_805_, v_k_806_, v_val_812_, v_l_808_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey(lean_object* v_00_u03b1_814_, lean_object* v_00_u03b2_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_k_818_, lean_object* v_f_819_, lean_object* v_l_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_Internal_List_alterKey___redArg(v_inst_816_, v_k_818_, v_f_819_, v_l_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object* v_x_822_, lean_object* v_h__1_823_, lean_object* v_h__2_824_){
_start:
{
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec(v_h__2_824_);
v___x_825_ = lean_box(0);
v___x_826_ = lean_apply_1(v_h__1_823_, v___x_825_);
return v___x_826_;
}
else
{
lean_object* v_val_827_; lean_object* v___x_828_; 
lean_dec(v_h__1_823_);
v_val_827_ = lean_ctor_get(v_x_822_, 0);
lean_inc(v_val_827_);
lean_dec_ref(v_x_822_);
v___x_828_ = lean_apply_1(v_h__2_824_, v_val_827_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_k_831_, lean_object* v_motive_832_, lean_object* v_x_833_, lean_object* v_h__1_834_, lean_object* v_h__2_835_){
_start:
{
if (lean_obj_tag(v_x_833_) == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_h__2_835_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_apply_1(v_h__1_834_, v___x_836_);
return v___x_837_;
}
else
{
lean_object* v_val_838_; lean_object* v___x_839_; 
lean_dec(v_h__1_834_);
v_val_838_ = lean_ctor_get(v_x_833_, 0);
lean_inc(v_val_838_);
lean_dec_ref(v_x_833_);
v___x_839_ = lean_apply_1(v_h__2_835_, v_val_838_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* v_00_u03b1_840_, lean_object* v_00_u03b2_841_, lean_object* v_k_842_, lean_object* v_motive_843_, lean_object* v_x_844_, lean_object* v_h__1_845_, lean_object* v_h__2_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_840_, v_00_u03b2_841_, v_k_842_, v_motive_843_, v_x_844_, v_h__1_845_, v_h__2_846_);
lean_dec(v_k_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_848_, lean_object* v_h__1_849_, lean_object* v_h__2_850_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v_h__2_850_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_apply_1(v_h__1_849_, v___x_851_);
return v___x_852_;
}
else
{
lean_object* v_val_853_; lean_object* v___x_854_; 
lean_dec(v_h__1_849_);
v_val_853_ = lean_ctor_get(v_x_848_, 0);
lean_inc(v_val_853_);
lean_dec_ref(v_x_848_);
v___x_854_ = lean_apply_1(v_h__2_850_, v_val_853_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_855_, lean_object* v_00_u03b2_856_, lean_object* v_k_857_, lean_object* v_motive_858_, lean_object* v_x_859_, lean_object* v_h__1_860_, lean_object* v_h__2_861_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v_h__2_861_);
v___x_862_ = lean_box(0);
v___x_863_ = lean_apply_1(v_h__1_860_, v___x_862_);
return v___x_863_;
}
else
{
lean_object* v_val_864_; lean_object* v___x_865_; 
lean_dec(v_h__1_860_);
v_val_864_ = lean_ctor_get(v_x_859_, 0);
lean_inc(v_val_864_);
lean_dec_ref(v_x_859_);
v___x_865_ = lean_apply_1(v_h__2_861_, v_val_864_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_866_, lean_object* v_00_u03b2_867_, lean_object* v_k_868_, lean_object* v_motive_869_, lean_object* v_x_870_, lean_object* v_h__1_871_, lean_object* v_h__2_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_866_, v_00_u03b2_867_, v_k_868_, v_motive_869_, v_x_870_, v_h__1_871_, v_h__2_872_);
lean_dec(v_k_868_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey___redArg(lean_object* v_inst_874_, lean_object* v_k_875_, lean_object* v_f_876_, lean_object* v_l_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_inc(v_l_877_);
lean_inc(v_k_875_);
lean_inc_ref(v_inst_874_);
v___x_878_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_874_, v_k_875_, v_l_877_);
v___x_879_ = lean_apply_1(v_f_876_, v___x_878_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_880_; 
v___x_880_ = l_Std_Internal_List_eraseKey___redArg(v_inst_874_, v_k_875_, v_l_877_);
return v___x_880_;
}
else
{
lean_object* v_val_881_; lean_object* v___x_882_; 
v_val_881_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_val_881_);
lean_dec_ref(v___x_879_);
v___x_882_ = l_Std_Internal_List_insertEntry___redArg(v_inst_874_, v_k_875_, v_val_881_, v_l_877_);
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey(lean_object* v_00_u03b1_883_, lean_object* v_00_u03b2_884_, lean_object* v_inst_885_, lean_object* v_k_886_, lean_object* v_f_887_, lean_object* v_l_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Std_Internal_List_Const_alterKey___redArg(v_inst_885_, v_k_886_, v_f_887_, v_l_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object* v_x_890_, lean_object* v_h__1_891_, lean_object* v_h__2_892_){
_start:
{
if (lean_obj_tag(v_x_890_) == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec(v_h__2_892_);
v___x_893_ = lean_box(0);
v___x_894_ = lean_apply_1(v_h__1_891_, v___x_893_);
return v___x_894_;
}
else
{
lean_object* v_val_895_; lean_object* v___x_896_; 
lean_dec(v_h__1_891_);
v_val_895_ = lean_ctor_get(v_x_890_, 0);
lean_inc(v_val_895_);
lean_dec_ref(v_x_890_);
v___x_896_ = lean_apply_1(v_h__2_892_, v_val_895_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* v_00_u03b2_897_, lean_object* v_motive_898_, lean_object* v_x_899_, lean_object* v_h__1_900_, lean_object* v_h__2_901_){
_start:
{
if (lean_obj_tag(v_x_899_) == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v_h__2_901_);
v___x_902_ = lean_box(0);
v___x_903_ = lean_apply_1(v_h__1_900_, v___x_902_);
return v___x_903_;
}
else
{
lean_object* v_val_904_; lean_object* v___x_905_; 
lean_dec(v_h__1_900_);
v_val_904_ = lean_ctor_get(v_x_899_, 0);
lean_inc(v_val_904_);
lean_dec_ref(v_x_899_);
v___x_905_ = lean_apply_1(v_h__2_901_, v_val_904_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_906_, lean_object* v_h__1_907_, lean_object* v_h__2_908_){
_start:
{
if (lean_obj_tag(v_x_906_) == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_h__2_908_);
v___x_909_ = lean_box(0);
v___x_910_ = lean_apply_1(v_h__1_907_, v___x_909_);
return v___x_910_;
}
else
{
lean_object* v_val_911_; lean_object* v___x_912_; 
lean_dec(v_h__1_907_);
v_val_911_ = lean_ctor_get(v_x_906_, 0);
lean_inc(v_val_911_);
lean_dec_ref(v_x_906_);
v___x_912_ = lean_apply_1(v_h__2_908_, v_val_911_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b2_913_, lean_object* v_motive_914_, lean_object* v_x_915_, lean_object* v_h__1_916_, lean_object* v_h__2_917_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec(v_h__2_917_);
v___x_918_ = lean_box(0);
v___x_919_ = lean_apply_1(v_h__1_916_, v___x_918_);
return v___x_919_;
}
else
{
lean_object* v_val_920_; lean_object* v___x_921_; 
lean_dec(v_h__1_916_);
v_val_920_ = lean_ctor_get(v_x_915_, 0);
lean_inc(v_val_920_);
lean_dec_ref(v_x_915_);
v___x_921_ = lean_apply_1(v_h__2_917_, v_val_920_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey___redArg(lean_object* v_inst_922_, lean_object* v_k_923_, lean_object* v_f_924_, lean_object* v_l_925_){
_start:
{
lean_object* v___x_926_; 
lean_inc(v_l_925_);
lean_inc(v_k_923_);
lean_inc_ref(v_inst_922_);
v___x_926_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_922_, v_k_923_, v_l_925_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_dec(v_f_924_);
lean_dec(v_k_923_);
lean_dec_ref(v_inst_922_);
return v_l_925_;
}
else
{
lean_object* v_val_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_val_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_val_927_);
lean_dec_ref(v___x_926_);
v___x_928_ = lean_apply_1(v_f_924_, v_val_927_);
v___x_929_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_922_, v_k_923_, v___x_928_, v_l_925_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey(lean_object* v_00_u03b1_930_, lean_object* v_00_u03b2_931_, lean_object* v_inst_932_, lean_object* v_inst_933_, lean_object* v_k_934_, lean_object* v_f_935_, lean_object* v_l_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_Internal_List_modifyKey___redArg(v_inst_932_, v_k_934_, v_f_935_, v_l_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey___redArg(lean_object* v_inst_938_, lean_object* v_k_939_, lean_object* v_f_940_, lean_object* v_l_941_){
_start:
{
lean_object* v___x_942_; 
lean_inc(v_l_941_);
lean_inc(v_k_939_);
lean_inc_ref(v_inst_938_);
v___x_942_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_938_, v_k_939_, v_l_941_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_dec(v_f_940_);
lean_dec(v_k_939_);
lean_dec_ref(v_inst_938_);
return v_l_941_;
}
else
{
lean_object* v_val_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_val_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_val_943_);
lean_dec_ref(v___x_942_);
v___x_944_ = lean_apply_1(v_f_940_, v_val_943_);
v___x_945_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_938_, v_k_939_, v___x_944_, v_l_941_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_inst_948_, lean_object* v_k_949_, lean_object* v_f_950_, lean_object* v_l_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_Internal_List_Const_modifyKey___redArg(v_inst_948_, v_k_949_, v_f_950_, v_l_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_953_, lean_object* v_h__1_954_, lean_object* v_h__2_955_){
_start:
{
if (lean_obj_tag(v_x_953_) == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec(v_h__1_954_);
v___x_956_ = lean_box(0);
v___x_957_ = lean_apply_1(v_h__2_955_, v___x_956_);
return v___x_957_;
}
else
{
lean_object* v_val_958_; lean_object* v___x_959_; 
lean_dec(v_h__2_955_);
v_val_958_ = lean_ctor_get(v_x_953_, 0);
lean_inc(v_val_958_);
lean_dec_ref(v_x_953_);
v___x_959_ = lean_apply_1(v_h__1_954_, v_val_958_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_960_, lean_object* v_motive_961_, lean_object* v_x_962_, lean_object* v_h__1_963_, lean_object* v_h__2_964_){
_start:
{
if (lean_obj_tag(v_x_962_) == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_h__1_963_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_apply_1(v_h__2_964_, v___x_965_);
return v___x_966_;
}
else
{
lean_object* v_val_967_; lean_object* v___x_968_; 
lean_dec(v_h__2_964_);
v_val_967_ = lean_ctor_get(v_x_962_, 0);
lean_inc(v_val_967_);
lean_dec_ref(v_x_962_);
v___x_968_ = lean_apply_1(v_h__1_963_, v_val_967_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList___redArg(lean_object* v_inst_969_, lean_object* v_l_970_, lean_object* v_toErase_971_){
_start:
{
if (lean_obj_tag(v_toErase_971_) == 0)
{
lean_dec_ref(v_inst_969_);
return v_l_970_;
}
else
{
lean_object* v_head_972_; lean_object* v_tail_973_; lean_object* v___x_974_; 
v_head_972_ = lean_ctor_get(v_toErase_971_, 0);
lean_inc(v_head_972_);
v_tail_973_ = lean_ctor_get(v_toErase_971_, 1);
lean_inc(v_tail_973_);
lean_dec_ref(v_toErase_971_);
lean_inc_ref(v_inst_969_);
v___x_974_ = l_Std_Internal_List_eraseKey___redArg(v_inst_969_, v_head_972_, v_l_970_);
v_l_970_ = v___x_974_;
v_toErase_971_ = v_tail_973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList(lean_object* v_00_u03b1_976_, lean_object* v_00_u03b2_977_, lean_object* v_inst_978_, lean_object* v_l_979_, lean_object* v_toErase_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_Internal_List_eraseList___redArg(v_inst_978_, v_l_979_, v_toErase_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_982_, lean_object* v_h__1_983_, lean_object* v_h__2_984_){
_start:
{
if (lean_obj_tag(v_opt_982_) == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec(v_h__1_983_);
v___x_985_ = lean_box(0);
v___x_986_ = lean_apply_1(v_h__2_984_, v___x_985_);
return v___x_986_;
}
else
{
lean_object* v_val_987_; lean_object* v___x_988_; 
lean_dec(v_h__2_984_);
v_val_987_ = lean_ctor_get(v_opt_982_, 0);
lean_inc(v_val_987_);
lean_dec_ref(v_opt_982_);
v___x_988_ = lean_apply_1(v_h__1_983_, v_val_987_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_989_, lean_object* v_motive_990_, lean_object* v_opt_991_, lean_object* v_h__1_992_, lean_object* v_h__2_993_){
_start:
{
if (lean_obj_tag(v_opt_991_) == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v_h__1_992_);
v___x_994_ = lean_box(0);
v___x_995_ = lean_apply_1(v_h__2_993_, v___x_994_);
return v___x_995_;
}
else
{
lean_object* v_val_996_; lean_object* v___x_997_; 
lean_dec(v_h__2_993_);
v_val_996_ = lean_ctor_get(v_opt_991_, 0);
lean_inc(v_val_996_);
lean_dec_ref(v_opt_991_);
v___x_997_ = lean_apply_1(v_h__1_992_, v_val_996_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_inst_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___boxed(lean_object* v_00_u03b1_1002_, lean_object* v_00_u03b2_1003_, lean_object* v_inst_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(v_00_u03b1_1002_, v_00_u03b2_1003_, v_inst_1004_);
lean_dec_ref(v_inst_1004_);
return v_res_1005_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(lean_object* v_inst_1006_, lean_object* v_a_1007_, lean_object* v_b_1008_){
_start:
{
lean_object* v_fst_1009_; lean_object* v_fst_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_fst_1009_ = lean_ctor_get(v_a_1007_, 0);
lean_inc(v_fst_1009_);
lean_dec_ref(v_a_1007_);
v_fst_1010_ = lean_ctor_get(v_b_1008_, 0);
lean_inc(v_fst_1010_);
lean_dec_ref(v_b_1008_);
v___x_1011_ = lean_apply_2(v_inst_1006_, v_fst_1009_, v_fst_1010_);
v___x_1012_ = lean_unbox(v___x_1011_);
if (v___x_1012_ == 2)
{
uint8_t v___x_1013_; 
v___x_1013_ = 0;
return v___x_1013_;
}
else
{
uint8_t v___x_1014_; 
v___x_1014_ = 1;
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg___boxed(lean_object* v_inst_1015_, lean_object* v_a_1016_, lean_object* v_b_1017_){
_start:
{
uint8_t v_res_1018_; lean_object* v_r_1019_; 
v_res_1018_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_1015_, v_a_1016_, v_b_1017_);
v_r_1019_ = lean_box(v_res_1018_);
return v_r_1019_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_inst_1022_, lean_object* v_a_1023_, lean_object* v_b_1024_){
_start:
{
uint8_t v___x_1025_; 
v___x_1025_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_1022_, v_a_1023_, v_b_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_00_u03b2_1027_, lean_object* v_inst_1028_, lean_object* v_a_1029_, lean_object* v_b_1030_){
_start:
{
uint8_t v_res_1031_; lean_object* v_r_1032_; 
v_res_1031_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(v_00_u03b1_1026_, v_00_u03b2_1027_, v_inst_1028_, v_a_1029_, v_b_1030_);
v_r_1032_ = lean_box(v_res_1031_);
return v_r_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0(lean_object* v_inst_1033_, lean_object* v_a_1034_, lean_object* v_b_1035_){
_start:
{
lean_object* v_fst_1036_; lean_object* v_fst_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_fst_1036_ = lean_ctor_get(v_a_1034_, 0);
v_fst_1037_ = lean_ctor_get(v_b_1035_, 0);
lean_inc(v_fst_1037_);
lean_inc(v_fst_1036_);
v___x_1038_ = lean_apply_2(v_inst_1033_, v_fst_1036_, v_fst_1037_);
v___x_1039_ = lean_unbox(v___x_1038_);
if (v___x_1039_ == 2)
{
lean_dec_ref(v_a_1034_);
return v_b_1035_;
}
else
{
lean_dec_ref(v_b_1035_);
return v_a_1034_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg(lean_object* v_inst_1040_){
_start:
{
lean_object* v___f_1041_; 
v___f_1041_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1041_, 0, v_inst_1040_);
return v___f_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_inst_1044_){
_start:
{
lean_object* v___f_1045_; 
v___f_1045_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1045_, 0, v_inst_1044_);
return v___f_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___redArg(lean_object* v_inst_1046_, lean_object* v_xs_1047_){
_start:
{
lean_object* v___f_1048_; lean_object* v___x_1049_; 
v___f_1048_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1048_, 0, v_inst_1046_);
v___x_1049_ = l_List_min_x3f___redArg(v___f_1048_, v_xs_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_inst_1052_, lean_object* v_xs_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_1052_, v_xs_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___redArg(lean_object* v_inst_1055_, lean_object* v_xs_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_1055_, v_xs_1056_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_box(0);
return v___x_1058_;
}
else
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1067_; 
v_val_1059_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1061_ = v___x_1057_;
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v___x_1057_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_fst_1063_; lean_object* v___x_1065_; 
v_fst_1063_ = lean_ctor_get(v_val_1059_, 0);
lean_inc(v_fst_1063_);
lean_dec(v_val_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v_fst_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_fst_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_inst_1070_, lean_object* v_xs_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1070_, v_xs_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___redArg(lean_object* v_x_1073_, lean_object* v_h__1_1074_, lean_object* v_h__2_1075_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v_h__2_1075_);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_apply_1(v_h__1_1074_, v___x_1076_);
return v___x_1077_;
}
else
{
lean_object* v_val_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__1_1074_);
v_val_1078_ = lean_ctor_get(v_x_1073_, 0);
lean_inc(v_val_1078_);
lean_dec_ref(v_x_1073_);
v___x_1079_ = lean_apply_1(v_h__2_1075_, v_val_1078_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter(lean_object* v_00_u03b1_1080_, lean_object* v_00_u03b2_1081_, lean_object* v_motive_1082_, lean_object* v_x_1083_, lean_object* v_h__1_1084_, lean_object* v_h__2_1085_){
_start:
{
if (lean_obj_tag(v_x_1083_) == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v_h__2_1085_);
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_apply_1(v_h__1_1084_, v___x_1086_);
return v___x_1087_;
}
else
{
lean_object* v_val_1088_; lean_object* v___x_1089_; 
lean_dec(v_h__1_1084_);
v_val_1088_ = lean_ctor_get(v_x_1083_, 0);
lean_inc(v_val_1088_);
lean_dec_ref(v_x_1083_);
v___x_1089_ = lean_apply_1(v_h__2_1085_, v_val_1088_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_1090_, lean_object* v_h__1_1091_, lean_object* v_h__2_1092_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec(v_h__2_1092_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_apply_1(v_h__1_1091_, v___x_1093_);
return v___x_1094_;
}
else
{
lean_object* v_head_1095_; lean_object* v_tail_1096_; lean_object* v___x_1097_; 
lean_dec(v_h__1_1091_);
v_head_1095_ = lean_ctor_get(v_x_1090_, 0);
lean_inc(v_head_1095_);
v_tail_1096_ = lean_ctor_get(v_x_1090_, 1);
lean_inc(v_tail_1096_);
lean_dec_ref(v_x_1090_);
v___x_1097_ = lean_apply_2(v_h__2_1092_, v_head_1095_, v_tail_1096_);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_1098_, lean_object* v_motive_1099_, lean_object* v_x_1100_, lean_object* v_h__1_1101_, lean_object* v_h__2_1102_){
_start:
{
if (lean_obj_tag(v_x_1100_) == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec(v_h__2_1102_);
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_apply_1(v_h__1_1101_, v___x_1103_);
return v___x_1104_;
}
else
{
lean_object* v_head_1105_; lean_object* v_tail_1106_; lean_object* v___x_1107_; 
lean_dec(v_h__1_1101_);
v_head_1105_ = lean_ctor_get(v_x_1100_, 0);
lean_inc(v_head_1105_);
v_tail_1106_ = lean_ctor_get(v_x_1100_, 1);
lean_inc(v_tail_1106_);
lean_dec_ref(v_x_1100_);
v___x_1107_ = lean_apply_2(v_h__2_1102_, v_head_1105_, v_tail_1106_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter___redArg(lean_object* v_x_1108_, lean_object* v_h__1_1109_, lean_object* v_h__2_1110_){
_start:
{
if (lean_obj_tag(v_x_1108_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v_h__2_1110_);
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_apply_1(v_h__1_1109_, v___x_1111_);
return v___x_1112_;
}
else
{
lean_object* v_val_1113_; lean_object* v___x_1114_; 
lean_dec(v_h__1_1109_);
v_val_1113_ = lean_ctor_get(v_x_1108_, 0);
lean_inc(v_val_1113_);
lean_dec_ref(v_x_1108_);
v___x_1114_ = lean_apply_1(v_h__2_1110_, v_val_1113_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter(lean_object* v_00_u03b1_1115_, lean_object* v_00_u03b2_1116_, lean_object* v_motive_1117_, lean_object* v_x_1118_, lean_object* v_h__1_1119_, lean_object* v_h__2_1120_){
_start:
{
if (lean_obj_tag(v_x_1118_) == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec(v_h__2_1120_);
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_apply_1(v_h__1_1119_, v___x_1121_);
return v___x_1122_;
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1124_; 
lean_dec(v_h__1_1119_);
v_val_1123_ = lean_ctor_get(v_x_1118_, 0);
lean_inc(v_val_1123_);
lean_dec_ref(v_x_1118_);
v___x_1124_ = lean_apply_1(v_h__2_1120_, v_val_1123_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___redArg(lean_object* v_inst_1125_, lean_object* v_xs_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v_val_1128_; 
v___x_1127_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1125_, v_xs_1126_);
v_val_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_val_1128_);
lean_dec(v___x_1127_);
return v_val_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_inst_1131_, lean_object* v_xs_1132_, lean_object* v_h_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Std_Internal_List_minKey___redArg(v_inst_1131_, v_xs_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___redArg(lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_xs_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1135_, v_xs_1137_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_1140_ = l_panic___redArg(v_inst_1136_, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v_val_1141_; 
lean_dec(v_inst_1136_);
v_val_1141_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_val_1141_);
lean_dec_ref(v___x_1138_);
return v_val_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21(lean_object* v_00_u03b1_1142_, lean_object* v_00_u03b2_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_xs_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_1144_, v_inst_1145_, v_xs_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg(lean_object* v_inst_1148_, lean_object* v_xs_1149_, lean_object* v_fallback_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1148_, v_xs_1149_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_inc(v_fallback_1150_);
return v_fallback_1150_;
}
else
{
lean_object* v_val_1152_; 
v_val_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1152_);
lean_dec_ref(v___x_1151_);
return v_val_1152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg___boxed(lean_object* v_inst_1153_, lean_object* v_xs_1154_, lean_object* v_fallback_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_Internal_List_minKeyD___redArg(v_inst_1153_, v_xs_1154_, v_fallback_1155_);
lean_dec(v_fallback_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_inst_1159_, lean_object* v_xs_1160_, lean_object* v_fallback_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Std_Internal_List_minKeyD___redArg(v_inst_1159_, v_xs_1160_, v_fallback_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___boxed(lean_object* v_00_u03b1_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_inst_1165_, lean_object* v_xs_1166_, lean_object* v_fallback_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_Internal_List_minKeyD(v_00_u03b1_1163_, v_00_u03b2_1164_, v_inst_1165_, v_xs_1166_, v_fallback_1167_);
lean_dec(v_fallback_1167_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f___redArg(lean_object* v_inst_1169_, lean_object* v_xs_1170_){
_start:
{
lean_object* v___f_1171_; lean_object* v___x_1172_; 
v___f_1171_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1171_, 0, v_inst_1169_);
v___x_1172_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1171_, v_xs_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f(lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_inst_1175_, lean_object* v_xs_1176_){
_start:
{
lean_object* v___f_1177_; lean_object* v___x_1178_; 
v___f_1177_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1177_, 0, v_inst_1175_);
v___x_1178_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1177_, v_xs_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey___redArg(lean_object* v_inst_1179_, lean_object* v_xs_1180_){
_start:
{
lean_object* v___f_1181_; lean_object* v___x_1182_; 
v___f_1181_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1181_, 0, v_inst_1179_);
v___x_1182_ = l_Std_Internal_List_minKey___redArg(v___f_1181_, v_xs_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_inst_1185_, lean_object* v_xs_1186_, lean_object* v_h_1187_){
_start:
{
lean_object* v___f_1188_; lean_object* v___x_1189_; 
v___f_1188_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1188_, 0, v_inst_1185_);
v___x_1189_ = l_Std_Internal_List_minKey___redArg(v___f_1188_, v_xs_1186_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg(lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_xs_1192_){
_start:
{
lean_object* v___f_1193_; lean_object* v___x_1194_; 
v___f_1193_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1193_, 0, v_inst_1190_);
v___x_1194_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1193_, v_xs_1192_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_1196_ = l_panic___redArg(v_inst_1191_, v___x_1195_);
return v___x_1196_;
}
else
{
lean_object* v_val_1197_; 
lean_dec(v_inst_1191_);
v_val_1197_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_val_1197_);
lean_dec_ref(v___x_1194_);
return v_val_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_xs_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_1200_, v_inst_1201_, v_xs_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg(lean_object* v_inst_1204_, lean_object* v_xs_1205_, lean_object* v_fallback_1206_){
_start:
{
lean_object* v___f_1207_; lean_object* v___x_1208_; 
v___f_1207_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1207_, 0, v_inst_1204_);
v___x_1208_ = l_Std_Internal_List_minKeyD___redArg(v___f_1207_, v_xs_1205_, v_fallback_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg___boxed(lean_object* v_inst_1209_, lean_object* v_xs_1210_, lean_object* v_fallback_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Std_Internal_List_maxKeyD___redArg(v_inst_1209_, v_xs_1210_, v_fallback_1211_);
lean_dec(v_fallback_1211_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD(lean_object* v_00_u03b1_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_inst_1215_, lean_object* v_xs_1216_, lean_object* v_fallback_1217_){
_start:
{
lean_object* v___f_1218_; lean_object* v___x_1219_; 
v___f_1218_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1218_, 0, v_inst_1215_);
v___x_1219_ = l_Std_Internal_List_minKeyD___redArg(v___f_1218_, v_xs_1216_, v_fallback_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_inst_1222_, lean_object* v_xs_1223_, lean_object* v_fallback_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Std_Internal_List_maxKeyD(v_00_u03b1_1220_, v_00_u03b2_1221_, v_inst_1222_, v_xs_1223_, v_fallback_1224_);
lean_dec(v_fallback_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn___redArg(lean_object* v_inst_1226_, lean_object* v_l_1227_, lean_object* v_sofar_1228_, lean_object* v_k_1229_){
_start:
{
lean_object* v___x_1230_; 
lean_inc_ref(v_inst_1226_);
v___x_1230_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_1226_, v_k_1229_, v_l_1227_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_dec_ref(v_inst_1226_);
return v_sofar_1228_;
}
else
{
lean_object* v_val_1231_; lean_object* v_fst_1232_; lean_object* v_snd_1233_; lean_object* v___x_1234_; 
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref(v___x_1230_);
v_fst_1232_ = lean_ctor_get(v_val_1231_, 0);
lean_inc(v_fst_1232_);
v_snd_1233_ = lean_ctor_get(v_val_1231_, 1);
lean_inc(v_snd_1233_);
lean_dec(v_val_1231_);
v___x_1234_ = l_Std_Internal_List_insertEntry___redArg(v_inst_1226_, v_fst_1232_, v_snd_1233_, v_sofar_1228_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn(lean_object* v_00_u03b1_1235_, lean_object* v_00_u03b2_1236_, lean_object* v_inst_1237_, lean_object* v_l_1238_, lean_object* v_sofar_1239_, lean_object* v_k_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Std_Internal_List_interSmallerFn___redArg(v_inst_1237_, v_l_1238_, v_sofar_1239_, v_k_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_1242_, lean_object* v_h__1_1243_, lean_object* v_h__2_1244_){
_start:
{
if (lean_obj_tag(v_x_1242_) == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v_h__1_1243_);
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_apply_1(v_h__2_1244_, v___x_1245_);
return v___x_1246_;
}
else
{
lean_object* v_val_1247_; lean_object* v___x_1248_; 
lean_dec(v_h__2_1244_);
v_val_1247_ = lean_ctor_get(v_x_1242_, 0);
lean_inc(v_val_1247_);
lean_dec_ref(v_x_1242_);
v___x_1248_ = lean_apply_1(v_h__1_1243_, v_val_1247_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_1249_, lean_object* v_00_u03b2_1250_, lean_object* v_motive_1251_, lean_object* v_x_1252_, lean_object* v_h__1_1253_, lean_object* v_h__2_1254_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec(v_h__1_1253_);
v___x_1255_ = lean_box(0);
v___x_1256_ = lean_apply_1(v_h__2_1254_, v___x_1255_);
return v___x_1256_;
}
else
{
lean_object* v_val_1257_; lean_object* v___x_1258_; 
lean_dec(v_h__2_1254_);
v_val_1257_ = lean_ctor_get(v_x_1252_, 0);
lean_inc(v_val_1257_);
lean_dec_ref(v_x_1252_);
v___x_1258_ = lean_apply_1(v_h__1_1253_, v_val_1257_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg___lam__0(lean_object* v_inst_1259_, lean_object* v_l_u2081_1260_, lean_object* v_sofar_1261_, lean_object* v_kv_1262_){
_start:
{
lean_object* v_fst_1263_; lean_object* v___x_1264_; 
v_fst_1263_ = lean_ctor_get(v_kv_1262_, 0);
lean_inc(v_fst_1263_);
lean_dec_ref(v_kv_1262_);
v___x_1264_ = l_Std_Internal_List_interSmallerFn___redArg(v_inst_1259_, v_l_u2081_1260_, v_sofar_1261_, v_fst_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg(lean_object* v_inst_1265_, lean_object* v_l_u2081_1266_, lean_object* v_l_u2082_1267_){
_start:
{
lean_object* v___f_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___f_1268_ = lean_alloc_closure((void*)(l_Std_Internal_List_interSmaller___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1268_, 0, v_inst_1265_);
lean_closure_set(v___f_1268_, 1, v_l_u2081_1266_);
v___x_1269_ = lean_box(0);
v___x_1270_ = l_List_foldl___redArg(v___f_1268_, v___x_1269_, v_l_u2082_1267_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller(lean_object* v_00_u03b1_1271_, lean_object* v_00_u03b2_1272_, lean_object* v_inst_1273_, lean_object* v_l_u2081_1274_, lean_object* v_l_u2082_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Std_Internal_List_interSmaller___redArg(v_inst_1273_, v_l_u2081_1274_, v_l_u2082_1275_);
return v___x_1276_;
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
