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
lean_object* v___x_91_; 
v___x_91_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(v_x_88_, v_h__1_89_, v_h__2_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___redArg(lean_object* v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v_h__2_94_);
v___x_95_ = lean_box(0);
v___x_96_ = lean_apply_1(v_h__1_93_, v___x_95_);
return v___x_96_;
}
else
{
lean_object* v_head_97_; lean_object* v_tail_98_; lean_object* v_fst_99_; lean_object* v_snd_100_; lean_object* v___x_101_; 
lean_dec(v_h__1_93_);
v_head_97_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_head_97_);
v_tail_98_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_tail_98_);
lean_dec_ref(v_x_92_);
v_fst_99_ = lean_ctor_get(v_head_97_, 0);
lean_inc(v_fst_99_);
v_snd_100_ = lean_ctor_get(v_head_97_, 1);
lean_inc(v_snd_100_);
lean_dec(v_head_97_);
v___x_101_ = lean_apply_3(v_h__2_94_, v_fst_99_, v_snd_100_, v_tail_98_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter(lean_object* v_00_u03b1_102_, lean_object* v_00_u03b2_103_, lean_object* v_motive_104_, lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___redArg(v_x_105_, v_h__1_106_, v_h__2_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter___redArg(lean_object* v_x_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_h__2_111_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_apply_1(v_h__1_110_, v___x_112_);
return v___x_113_;
}
else
{
lean_object* v_head_114_; lean_object* v_tail_115_; lean_object* v_fst_116_; lean_object* v_snd_117_; lean_object* v___x_118_; 
lean_dec(v_h__1_110_);
v_head_114_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_head_114_);
v_tail_115_ = lean_ctor_get(v_x_109_, 1);
lean_inc(v_tail_115_);
lean_dec_ref(v_x_109_);
v_fst_116_ = lean_ctor_get(v_head_114_, 0);
lean_inc(v_fst_116_);
v_snd_117_ = lean_ctor_get(v_head_114_, 1);
lean_inc(v_snd_117_);
lean_dec(v_head_114_);
v___x_118_ = lean_apply_3(v_h__2_111_, v_fst_116_, v_snd_117_, v_tail_115_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_motive_121_, lean_object* v_x_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_values_match__1_splitter___redArg(v_x_122_, v_h__1_123_, v_h__2_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f___redArg(lean_object* v_inst_126_, lean_object* v_a_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v___x_129_; 
lean_dec(v_a_127_);
lean_dec_ref(v_inst_126_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v_head_130_; lean_object* v_tail_131_; lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_head_130_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_head_130_);
v_tail_131_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_tail_131_);
lean_dec_ref(v_x_128_);
v_fst_132_ = lean_ctor_get(v_head_130_, 0);
lean_inc(v_fst_132_);
v_snd_133_ = lean_ctor_get(v_head_130_, 1);
lean_inc(v_snd_133_);
lean_dec(v_head_130_);
lean_inc_ref(v_inst_126_);
lean_inc(v_a_127_);
v___x_134_ = lean_apply_2(v_inst_126_, v_fst_132_, v_a_127_);
v___x_135_ = lean_unbox(v___x_134_);
if (v___x_135_ == 0)
{
lean_dec(v_snd_133_);
v_x_128_ = v_tail_131_;
goto _start;
}
else
{
lean_object* v___x_137_; 
lean_dec(v_tail_131_);
lean_dec(v_a_127_);
lean_dec_ref(v_inst_126_);
v___x_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_137_, 0, v_snd_133_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f(lean_object* v_00_u03b1_138_, lean_object* v_00_u03b2_139_, lean_object* v_inst_140_, lean_object* v_a_141_, lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_140_, v_a_141_, v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___redArg(lean_object* v_x_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_h__2_146_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_apply_1(v_h__1_145_, v___x_147_);
return v___x_148_;
}
else
{
lean_object* v_head_149_; lean_object* v_tail_150_; lean_object* v_fst_151_; lean_object* v_snd_152_; lean_object* v___x_153_; 
lean_dec(v_h__1_145_);
v_head_149_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_head_149_);
v_tail_150_ = lean_ctor_get(v_x_144_, 1);
lean_inc(v_tail_150_);
lean_dec_ref(v_x_144_);
v_fst_151_ = lean_ctor_get(v_head_149_, 0);
lean_inc(v_fst_151_);
v_snd_152_ = lean_ctor_get(v_head_149_, 1);
lean_inc(v_snd_152_);
lean_dec(v_head_149_);
v___x_153_ = lean_apply_3(v_h__2_146_, v_fst_151_, v_snd_152_, v_tail_150_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter(lean_object* v_00_u03b1_154_, lean_object* v_00_u03b2_155_, lean_object* v_motive_156_, lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___redArg(v_x_157_, v_h__1_158_, v_h__2_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f___redArg(lean_object* v_inst_161_, lean_object* v_a_162_, lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v___x_164_; 
lean_dec(v_a_162_);
lean_dec_ref(v_inst_161_);
v___x_164_ = lean_box(0);
return v___x_164_;
}
else
{
lean_object* v_head_165_; lean_object* v_tail_166_; lean_object* v_fst_167_; lean_object* v_snd_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v_head_165_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_head_165_);
v_tail_166_ = lean_ctor_get(v_x_163_, 1);
lean_inc(v_tail_166_);
lean_dec_ref(v_x_163_);
v_fst_167_ = lean_ctor_get(v_head_165_, 0);
lean_inc(v_fst_167_);
v_snd_168_ = lean_ctor_get(v_head_165_, 1);
lean_inc(v_snd_168_);
lean_dec(v_head_165_);
lean_inc_ref(v_inst_161_);
lean_inc(v_a_162_);
v___x_169_ = lean_apply_2(v_inst_161_, v_fst_167_, v_a_162_);
v___x_170_ = lean_unbox(v___x_169_);
if (v___x_170_ == 0)
{
lean_dec(v_snd_168_);
v_x_163_ = v_tail_166_;
goto _start;
}
else
{
lean_object* v___x_172_; 
lean_dec(v_tail_166_);
lean_dec(v_a_162_);
lean_dec_ref(v_inst_161_);
v___x_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_172_, 0, v_snd_168_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_a_177_, lean_object* v_x_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_175_, v_a_177_, v_x_178_);
return v___x_179_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg___lam__0(lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_l_u2082_182_, lean_object* v_x_183_){
_start:
{
lean_object* v_fst_184_; lean_object* v_snd_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_fst_184_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_fst_184_);
v_snd_185_ = lean_ctor_get(v_x_183_, 1);
lean_inc(v_snd_185_);
lean_dec_ref(v_x_183_);
lean_inc(v_fst_184_);
v___x_186_ = lean_apply_1(v_inst_180_, v_fst_184_);
v___x_187_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_181_, v_fst_184_, v_l_u2082_182_);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v_snd_185_);
v___x_189_ = l_Option_instBEq_beq___redArg(v___x_186_, v___x_187_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___lam__0___boxed(lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_l_u2082_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Std_Internal_List_beqModel___redArg___lam__0(v_inst_190_, v_inst_191_, v_l_u2082_192_, v_x_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg(lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_l_u2081_198_, lean_object* v_l_u2082_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_200_ = l_List_lengthTR___redArg(v_l_u2081_198_);
v___x_201_ = l_List_lengthTR___redArg(v_l_u2082_199_);
v___x_202_ = lean_nat_dec_eq(v___x_200_, v___x_201_);
lean_dec(v___x_201_);
lean_dec(v___x_200_);
if (v___x_202_ == 0)
{
lean_dec(v_l_u2082_199_);
lean_dec(v_l_u2081_198_);
lean_dec_ref(v_inst_197_);
lean_dec_ref(v_inst_196_);
return v___x_202_;
}
else
{
lean_object* v___f_203_; uint8_t v___x_204_; 
v___f_203_ = lean_alloc_closure((void*)(l_Std_Internal_List_beqModel___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_203_, 0, v_inst_197_);
lean_closure_set(v___f_203_, 1, v_inst_196_);
lean_closure_set(v___f_203_, 2, v_l_u2082_199_);
v___x_204_ = l_List_all___redArg(v_l_u2081_198_, v___f_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___boxed(lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_l_u2081_207_, lean_object* v_l_u2082_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_Std_Internal_List_beqModel___redArg(v_inst_205_, v_inst_206_, v_l_u2081_207_, v_l_u2082_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel(lean_object* v_00_u03b1_211_, lean_object* v_00_u03b2_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_l_u2081_216_, lean_object* v_l_u2082_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = l_Std_Internal_List_beqModel___redArg(v_inst_213_, v_inst_215_, v_l_u2081_216_, v_l_u2082_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___boxed(lean_object* v_00_u03b1_219_, lean_object* v_00_u03b2_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_l_u2081_224_, lean_object* v_l_u2082_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Std_Internal_List_beqModel(v_00_u03b1_219_, v_00_u03b2_220_, v_inst_221_, v_inst_222_, v_inst_223_, v_l_u2081_224_, v_l_u2082_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter___redArg(lean_object* v_x_228_, lean_object* v_h__1_229_, lean_object* v_h__2_230_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec(v_h__2_230_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_apply_1(v_h__1_229_, v___x_231_);
return v___x_232_;
}
else
{
lean_object* v_head_233_; lean_object* v_tail_234_; lean_object* v_fst_235_; lean_object* v_snd_236_; lean_object* v___x_237_; 
lean_dec(v_h__1_229_);
v_head_233_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_head_233_);
v_tail_234_ = lean_ctor_get(v_x_228_, 1);
lean_inc(v_tail_234_);
lean_dec_ref(v_x_228_);
v_fst_235_ = lean_ctor_get(v_head_233_, 0);
lean_inc(v_fst_235_);
v_snd_236_ = lean_ctor_get(v_head_233_, 1);
lean_inc(v_snd_236_);
lean_dec(v_head_233_);
v___x_237_ = lean_apply_3(v_h__2_230_, v_fst_235_, v_snd_236_, v_tail_234_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter(lean_object* v_00_u03b1_238_, lean_object* v_00_u03b2_239_, lean_object* v_motive_240_, lean_object* v_x_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValueCast_x3f_match__1_splitter___redArg(v_x_241_, v_h__1_242_, v_h__2_243_);
return v___x_244_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg___lam__0(lean_object* v_inst_245_, lean_object* v_l_u2082_246_, lean_object* v_inst_247_, lean_object* v_x_248_){
_start:
{
lean_object* v_fst_249_; lean_object* v_snd_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_fst_249_ = lean_ctor_get(v_x_248_, 0);
lean_inc(v_fst_249_);
v_snd_250_ = lean_ctor_get(v_x_248_, 1);
lean_inc(v_snd_250_);
lean_dec_ref(v_x_248_);
v___x_251_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_245_, v_fst_249_, v_l_u2082_246_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v_snd_250_);
v___x_253_ = l_Option_instBEq_beq___redArg(v_inst_247_, v___x_251_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed(lean_object* v_inst_254_, lean_object* v_l_u2082_255_, lean_object* v_inst_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Std_Internal_List_Const_beqModel___redArg___lam__0(v_inst_254_, v_l_u2082_255_, v_inst_256_, v_x_257_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg(lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_l_u2081_262_, lean_object* v_l_u2082_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_264_ = l_List_lengthTR___redArg(v_l_u2081_262_);
v___x_265_ = l_List_lengthTR___redArg(v_l_u2082_263_);
v___x_266_ = lean_nat_dec_eq(v___x_264_, v___x_265_);
lean_dec(v___x_265_);
lean_dec(v___x_264_);
if (v___x_266_ == 0)
{
lean_dec(v_l_u2082_263_);
lean_dec(v_l_u2081_262_);
lean_dec_ref(v_inst_261_);
lean_dec_ref(v_inst_260_);
return v___x_266_;
}
else
{
lean_object* v___f_267_; uint8_t v___x_268_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_267_, 0, v_inst_260_);
lean_closure_set(v___f_267_, 1, v_l_u2082_263_);
lean_closure_set(v___f_267_, 2, v_inst_261_);
v___x_268_ = l_List_all___redArg(v_l_u2081_262_, v___f_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___boxed(lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_l_u2081_271_, lean_object* v_l_u2082_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_269_, v_inst_270_, v_l_u2081_271_, v_l_u2082_272_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel(lean_object* v_00_u03b1_275_, lean_object* v_00_u03b2_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_l_u2081_279_, lean_object* v_l_u2082_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_277_, v_inst_278_, v_l_u2081_279_, v_l_u2082_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___boxed(lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_l_u2081_286_, lean_object* v_l_u2082_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_Internal_List_Const_beqModel(v_00_u03b1_282_, v_00_u03b2_283_, v_inst_284_, v_inst_285_, v_l_u2081_286_, v_l_u2082_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v___x_292_; 
lean_dec(v_x_291_);
v___x_292_ = lean_box(0);
return v___x_292_;
}
else
{
lean_object* v_val_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
v_val_293_ = lean_ctor_get(v_x_290_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_301_ == 0)
{
v___x_295_ = v_x_290_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_val_293_);
lean_dec(v_x_290_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_apply_2(v_x_291_, v_val_293_, lean_box(0));
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap(lean_object* v_00_u03b1_302_, lean_object* v_00_u03b2_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(v_x_304_, v_x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___redArg(lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v___x_311_; 
lean_dec(v_h__2_310_);
v___x_311_ = lean_apply_1(v_h__1_309_, v_x_308_);
return v___x_311_;
}
else
{
lean_object* v_val_312_; lean_object* v___x_313_; 
lean_dec(v_h__1_309_);
v_val_312_ = lean_ctor_get(v_x_307_, 0);
lean_inc(v_val_312_);
lean_dec_ref(v_x_307_);
v___x_313_ = lean_apply_2(v_h__2_310_, v_val_312_, v_x_308_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_motive_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_h__1_319_, lean_object* v_h__2_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___redArg(v_x_317_, v_x_318_, v_h__1_319_, v_h__2_320_);
return v___x_321_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey___redArg(lean_object* v_inst_322_, lean_object* v_a_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
uint8_t v___x_325_; 
lean_dec(v_a_323_);
lean_dec_ref(v_inst_322_);
v___x_325_ = 0;
return v___x_325_;
}
else
{
lean_object* v_head_326_; lean_object* v_tail_327_; lean_object* v_fst_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_head_326_ = lean_ctor_get(v_x_324_, 0);
lean_inc(v_head_326_);
v_tail_327_ = lean_ctor_get(v_x_324_, 1);
lean_inc(v_tail_327_);
lean_dec_ref(v_x_324_);
v_fst_328_ = lean_ctor_get(v_head_326_, 0);
lean_inc(v_fst_328_);
lean_dec(v_head_326_);
lean_inc_ref(v_inst_322_);
lean_inc(v_a_323_);
v___x_329_ = lean_apply_2(v_inst_322_, v_fst_328_, v_a_323_);
v___x_330_ = lean_unbox(v___x_329_);
if (v___x_330_ == 0)
{
v_x_324_ = v_tail_327_;
goto _start;
}
else
{
uint8_t v___x_332_; 
lean_dec(v_tail_327_);
lean_dec(v_a_323_);
lean_dec_ref(v_inst_322_);
v___x_332_ = lean_unbox(v___x_329_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___redArg___boxed(lean_object* v_inst_333_, lean_object* v_a_334_, lean_object* v_x_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_Std_Internal_List_containsKey___redArg(v_inst_333_, v_a_334_, v_x_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey(lean_object* v_00_u03b1_338_, lean_object* v_00_u03b2_339_, lean_object* v_inst_340_, lean_object* v_a_341_, lean_object* v_x_342_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = l_Std_Internal_List_containsKey___redArg(v_inst_340_, v_a_341_, v_x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___boxed(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_inst_346_, lean_object* v_a_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_Internal_List_containsKey(v_00_u03b1_344_, v_00_u03b2_345_, v_inst_346_, v_a_347_, v_x_348_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry___redArg(lean_object* v_inst_351_, lean_object* v_a_352_, lean_object* v_l_353_){
_start:
{
lean_object* v___x_354_; lean_object* v_val_355_; 
v___x_354_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_351_, v_a_352_, v_l_353_);
v_val_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_val_355_);
lean_dec(v___x_354_);
return v_val_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_inst_358_, lean_object* v_a_359_, lean_object* v_l_360_, lean_object* v_h_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_Internal_List_getEntry___redArg(v_inst_358_, v_a_359_, v_l_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue___redArg(lean_object* v_inst_363_, lean_object* v_a_364_, lean_object* v_l_365_){
_start:
{
lean_object* v___x_366_; lean_object* v_val_367_; 
v___x_366_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_363_, v_a_364_, v_l_365_);
v_val_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_val_367_);
lean_dec(v___x_366_);
return v_val_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_inst_370_, lean_object* v_a_371_, lean_object* v_l_372_, lean_object* v_h_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_Internal_List_getValue___redArg(v_inst_370_, v_a_371_, v_l_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast___redArg(lean_object* v_inst_375_, lean_object* v_a_376_, lean_object* v_l_377_){
_start:
{
lean_object* v___x_378_; lean_object* v_val_379_; 
v___x_378_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_375_, v_a_376_, v_l_377_);
v_val_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_val_379_);
lean_dec(v___x_378_);
return v_val_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast(lean_object* v_00_u03b1_380_, lean_object* v_00_u03b2_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_a_384_, lean_object* v_l_385_, lean_object* v_h_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_Internal_List_getValueCast___redArg(v_inst_382_, v_a_384_, v_l_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg(lean_object* v_inst_388_, lean_object* v_a_389_, lean_object* v_l_390_, lean_object* v_fallback_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_388_, v_a_389_, v_l_390_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_inc(v_fallback_391_);
return v_fallback_391_;
}
else
{
lean_object* v_val_393_; 
v_val_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_val_393_);
lean_dec_ref(v___x_392_);
return v_val_393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg___boxed(lean_object* v_inst_394_, lean_object* v_a_395_, lean_object* v_l_396_, lean_object* v_fallback_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_Internal_List_getValueCastD___redArg(v_inst_394_, v_a_395_, v_l_396_, v_fallback_397_);
lean_dec(v_fallback_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_a_403_, lean_object* v_l_404_, lean_object* v_fallback_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_Internal_List_getValueCastD___redArg(v_inst_401_, v_a_403_, v_l_404_, v_fallback_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___boxed(lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_a_411_, lean_object* v_l_412_, lean_object* v_fallback_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Internal_List_getValueCastD(v_00_u03b1_407_, v_00_u03b2_408_, v_inst_409_, v_inst_410_, v_a_411_, v_l_412_, v_fallback_413_);
lean_dec(v_fallback_413_);
return v_res_414_;
}
}
static lean_object* _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_418_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__2));
v___x_419_ = lean_unsigned_to_nat(14u);
v___x_420_ = lean_unsigned_to_nat(22u);
v___x_421_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__1));
v___x_422_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__0));
v___x_423_ = l_mkPanicMessageWithDecl(v___x_422_, v___x_421_, v___x_420_, v___x_419_, v___x_418_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___redArg(lean_object* v_inst_424_, lean_object* v_a_425_, lean_object* v_inst_426_, lean_object* v_l_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_424_, v_a_425_, v_l_427_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_430_ = l_panic___redArg(v_inst_426_, v___x_429_);
return v___x_430_;
}
else
{
lean_object* v_val_431_; 
lean_dec(v_inst_426_);
v_val_431_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_val_431_);
lean_dec_ref(v___x_428_);
return v_val_431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21(lean_object* v_00_u03b1_432_, lean_object* v_00_u03b2_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_a_436_, lean_object* v_inst_437_, lean_object* v_l_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_Internal_List_getValueCast_x21___redArg(v_inst_434_, v_a_436_, v_inst_437_, v_l_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg(lean_object* v_inst_440_, lean_object* v_a_441_, lean_object* v_l_442_, lean_object* v_fallback_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_440_, v_a_441_, v_l_442_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_inc(v_fallback_443_);
return v_fallback_443_;
}
else
{
lean_object* v_val_445_; 
v_val_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_val_445_);
lean_dec_ref(v___x_444_);
return v_val_445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg___boxed(lean_object* v_inst_446_, lean_object* v_a_447_, lean_object* v_l_448_, lean_object* v_fallback_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_Internal_List_getValueD___redArg(v_inst_446_, v_a_447_, v_l_448_, v_fallback_449_);
lean_dec(v_fallback_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD(lean_object* v_00_u03b1_451_, lean_object* v_00_u03b2_452_, lean_object* v_inst_453_, lean_object* v_a_454_, lean_object* v_l_455_, lean_object* v_fallback_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_Internal_List_getValueD___redArg(v_inst_453_, v_a_454_, v_l_455_, v_fallback_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___boxed(lean_object* v_00_u03b1_458_, lean_object* v_00_u03b2_459_, lean_object* v_inst_460_, lean_object* v_a_461_, lean_object* v_l_462_, lean_object* v_fallback_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_Internal_List_getValueD(v_00_u03b1_458_, v_00_u03b2_459_, v_inst_460_, v_a_461_, v_l_462_, v_fallback_463_);
lean_dec(v_fallback_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg(lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_a_467_, lean_object* v_l_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_465_, v_a_467_, v_l_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_471_ = l_panic___redArg(v_inst_466_, v___x_470_);
return v___x_471_;
}
else
{
lean_object* v_val_472_; 
lean_dec(v_inst_466_);
v_val_472_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_472_);
lean_dec_ref(v___x_469_);
return v_val_472_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21(lean_object* v_00_u03b1_473_, lean_object* v_00_u03b2_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_a_477_, lean_object* v_l_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_Internal_List_getValue_x21___redArg(v_inst_475_, v_inst_476_, v_a_477_, v_l_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f___redArg(lean_object* v_inst_480_, lean_object* v_a_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v___x_483_; 
lean_dec(v_a_481_);
lean_dec_ref(v_inst_480_);
v___x_483_ = lean_box(0);
return v___x_483_;
}
else
{
lean_object* v_head_484_; lean_object* v_tail_485_; lean_object* v_fst_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_head_484_ = lean_ctor_get(v_x_482_, 0);
lean_inc(v_head_484_);
v_tail_485_ = lean_ctor_get(v_x_482_, 1);
lean_inc(v_tail_485_);
lean_dec_ref(v_x_482_);
v_fst_486_ = lean_ctor_get(v_head_484_, 0);
lean_inc(v_fst_486_);
lean_dec(v_head_484_);
lean_inc_ref(v_inst_480_);
lean_inc(v_a_481_);
lean_inc(v_fst_486_);
v___x_487_ = lean_apply_2(v_inst_480_, v_fst_486_, v_a_481_);
v___x_488_ = lean_unbox(v___x_487_);
if (v___x_488_ == 0)
{
lean_dec(v_fst_486_);
v_x_482_ = v_tail_485_;
goto _start;
}
else
{
lean_object* v___x_490_; 
lean_dec(v_tail_485_);
lean_dec(v_a_481_);
lean_dec_ref(v_inst_480_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_fst_486_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f(lean_object* v_00_u03b1_491_, lean_object* v_00_u03b2_492_, lean_object* v_inst_493_, lean_object* v_a_494_, lean_object* v_x_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_493_, v_a_494_, v_x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey___redArg(lean_object* v_inst_497_, lean_object* v_a_498_, lean_object* v_l_499_){
_start:
{
lean_object* v___x_500_; lean_object* v_val_501_; 
v___x_500_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_497_, v_a_498_, v_l_499_);
v_val_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_val_501_);
lean_dec(v___x_500_);
return v_val_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_inst_504_, lean_object* v_a_505_, lean_object* v_l_506_, lean_object* v_h_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_Internal_List_getKey___redArg(v_inst_504_, v_a_505_, v_l_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg(lean_object* v_inst_509_, lean_object* v_a_510_, lean_object* v_l_511_, lean_object* v_fallback_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_509_, v_a_510_, v_l_511_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_inc(v_fallback_512_);
return v_fallback_512_;
}
else
{
lean_object* v_val_514_; 
v_val_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_val_514_);
lean_dec_ref(v___x_513_);
return v_val_514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg___boxed(lean_object* v_inst_515_, lean_object* v_a_516_, lean_object* v_l_517_, lean_object* v_fallback_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_Internal_List_getKeyD___redArg(v_inst_515_, v_a_516_, v_l_517_, v_fallback_518_);
lean_dec(v_fallback_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_inst_522_, lean_object* v_a_523_, lean_object* v_l_524_, lean_object* v_fallback_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_Internal_List_getKeyD___redArg(v_inst_522_, v_a_523_, v_l_524_, v_fallback_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___boxed(lean_object* v_00_u03b1_527_, lean_object* v_00_u03b2_528_, lean_object* v_inst_529_, lean_object* v_a_530_, lean_object* v_l_531_, lean_object* v_fallback_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_Internal_List_getKeyD(v_00_u03b1_527_, v_00_u03b2_528_, v_inst_529_, v_a_530_, v_l_531_, v_fallback_532_);
lean_dec(v_fallback_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg(lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_a_536_, lean_object* v_l_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_534_, v_a_536_, v_l_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_540_ = l_panic___redArg(v_inst_535_, v___x_539_);
return v___x_540_;
}
else
{
lean_object* v_val_541_; 
lean_dec(v_inst_535_);
v_val_541_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_val_541_);
lean_dec_ref(v___x_538_);
return v_val_541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_a_546_, lean_object* v_l_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_Internal_List_getKey_x21___redArg(v_inst_544_, v_inst_545_, v_a_546_, v_l_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry___redArg(lean_object* v_inst_549_, lean_object* v_k_550_, lean_object* v_v_551_, lean_object* v_x_552_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_object* v___x_553_; 
lean_dec(v_v_551_);
lean_dec(v_k_550_);
lean_dec_ref(v_inst_549_);
v___x_553_ = lean_box(0);
return v___x_553_;
}
else
{
lean_object* v_head_554_; lean_object* v_tail_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_578_; 
v_head_554_ = lean_ctor_get(v_x_552_, 0);
v_tail_555_ = lean_ctor_get(v_x_552_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_578_ == 0)
{
v___x_557_ = v_x_552_;
v_isShared_558_ = v_isSharedCheck_578_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_tail_555_);
lean_inc(v_head_554_);
lean_dec(v_x_552_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_578_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_fst_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_fst_559_ = lean_ctor_get(v_head_554_, 0);
lean_inc_ref(v_inst_549_);
lean_inc(v_k_550_);
lean_inc(v_fst_559_);
v___x_560_ = lean_apply_2(v_inst_549_, v_fst_559_, v_k_550_);
v___x_561_ = lean_unbox(v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_562_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_549_, v_k_550_, v_v_551_, v_tail_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_562_);
v___x_564_ = v___x_557_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_head_554_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
else
{
lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_575_; 
lean_dec_ref(v_inst_549_);
v_isSharedCheck_575_ = !lean_is_exclusive(v_head_554_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; lean_object* v_unused_577_; 
v_unused_576_ = lean_ctor_get(v_head_554_, 1);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_head_554_, 0);
lean_dec(v_unused_577_);
v___x_567_ = v_head_554_;
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
else
{
lean_dec(v_head_554_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v_v_551_);
lean_ctor_set(v___x_567_, 0, v_k_550_);
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_k_550_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_v_551_);
v___x_570_ = v_reuseFailAlloc_574_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_572_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_570_);
v___x_572_ = v___x_557_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_tail_555_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_inst_581_, lean_object* v_k_582_, lean_object* v_v_583_, lean_object* v_x_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_581_, v_k_582_, v_v_583_, v_x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey___redArg(lean_object* v_inst_586_, lean_object* v_k_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
lean_object* v___x_589_; 
lean_dec(v_k_587_);
lean_dec_ref(v_inst_586_);
v___x_589_ = lean_box(0);
return v___x_589_;
}
else
{
lean_object* v_head_590_; lean_object* v_tail_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_602_; 
v_head_590_ = lean_ctor_get(v_x_588_, 0);
v_tail_591_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_602_ == 0)
{
v___x_593_ = v_x_588_;
v_isShared_594_ = v_isSharedCheck_602_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_tail_591_);
lean_inc(v_head_590_);
lean_dec(v_x_588_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_602_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_fst_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_fst_595_ = lean_ctor_get(v_head_590_, 0);
lean_inc_ref(v_inst_586_);
lean_inc(v_k_587_);
lean_inc(v_fst_595_);
v___x_596_ = lean_apply_2(v_inst_586_, v_fst_595_, v_k_587_);
v___x_597_ = lean_unbox(v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = l_Std_Internal_List_eraseKey___redArg(v_inst_586_, v_k_587_, v_tail_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v___x_598_);
v___x_600_ = v___x_593_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_head_590_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
else
{
lean_del_object(v___x_593_);
lean_dec(v_head_590_);
lean_dec(v_k_587_);
lean_dec_ref(v_inst_586_);
return v_tail_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey(lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_inst_605_, lean_object* v_k_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_Internal_List_eraseKey___redArg(v_inst_605_, v_k_606_, v_x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry___redArg(lean_object* v_inst_609_, lean_object* v_k_610_, lean_object* v_v_611_, lean_object* v_l_612_){
_start:
{
uint8_t v___x_613_; 
lean_inc(v_l_612_);
lean_inc(v_k_610_);
lean_inc_ref(v_inst_609_);
v___x_613_ = l_Std_Internal_List_containsKey___redArg(v_inst_609_, v_k_610_, v_l_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec_ref(v_inst_609_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v_k_610_);
lean_ctor_set(v___x_614_, 1, v_v_611_);
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_l_612_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_609_, v_k_610_, v_v_611_, v_l_612_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_inst_619_, lean_object* v_k_620_, lean_object* v_v_621_, lean_object* v_l_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_Internal_List_insertEntry___redArg(v_inst_619_, v_k_620_, v_v_621_, v_l_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew___redArg(lean_object* v_inst_624_, lean_object* v_k_625_, lean_object* v_v_626_, lean_object* v_l_627_){
_start:
{
uint8_t v___x_628_; 
lean_inc(v_l_627_);
lean_inc(v_k_625_);
v___x_628_ = l_Std_Internal_List_containsKey___redArg(v_inst_624_, v_k_625_, v_l_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_k_625_);
lean_ctor_set(v___x_629_, 1, v_v_626_);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_l_627_);
return v___x_630_;
}
else
{
lean_dec(v_v_626_);
lean_dec(v_k_625_);
return v_l_627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew(lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_inst_633_, lean_object* v_k_634_, lean_object* v_v_635_, lean_object* v_l_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_633_, v_k_634_, v_v_635_, v_l_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_638_, lean_object* v_h__1_639_, lean_object* v_h__2_640_){
_start:
{
if (lean_obj_tag(v_x_638_) == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec(v_h__2_640_);
v___x_641_ = lean_box(0);
v___x_642_ = lean_apply_1(v_h__1_639_, v___x_641_);
return v___x_642_;
}
else
{
lean_object* v_val_643_; lean_object* v___x_644_; 
lean_dec(v_h__1_639_);
v_val_643_ = lean_ctor_get(v_x_638_, 0);
lean_inc(v_val_643_);
lean_dec_ref(v_x_638_);
v___x_644_ = lean_apply_1(v_h__2_640_, v_val_643_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_645_, lean_object* v_motive_646_, lean_object* v_x_647_, lean_object* v_h__1_648_, lean_object* v_h__2_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___redArg(v_x_647_, v_h__1_648_, v_h__2_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_651_, lean_object* v_h__1_652_, lean_object* v_h__2_653_){
_start:
{
if (lean_obj_tag(v_x_651_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; 
lean_dec(v_h__2_653_);
v_a_654_ = lean_ctor_get(v_x_651_, 0);
lean_inc(v_a_654_);
lean_dec_ref(v_x_651_);
v___x_655_ = lean_apply_1(v_h__1_652_, v_a_654_);
return v___x_655_;
}
else
{
lean_object* v_a_656_; lean_object* v___x_657_; 
lean_dec(v_h__1_652_);
v_a_656_ = lean_ctor_get(v_x_651_, 0);
lean_inc(v_a_656_);
lean_dec_ref(v_x_651_);
v___x_657_ = lean_apply_1(v_h__2_653_, v_a_656_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_658_, lean_object* v_motive_659_, lean_object* v_x_660_, lean_object* v_h__1_661_, lean_object* v_h__2_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___redArg(v_x_660_, v_h__1_661_, v_h__2_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList___redArg(lean_object* v_inst_664_, lean_object* v_l_665_, lean_object* v_toInsert_666_){
_start:
{
if (lean_obj_tag(v_toInsert_666_) == 0)
{
lean_dec_ref(v_inst_664_);
return v_l_665_;
}
else
{
lean_object* v_head_667_; lean_object* v_tail_668_; lean_object* v_fst_669_; lean_object* v_snd_670_; lean_object* v___x_671_; 
v_head_667_ = lean_ctor_get(v_toInsert_666_, 0);
lean_inc(v_head_667_);
v_tail_668_ = lean_ctor_get(v_toInsert_666_, 1);
lean_inc(v_tail_668_);
lean_dec_ref(v_toInsert_666_);
v_fst_669_ = lean_ctor_get(v_head_667_, 0);
lean_inc(v_fst_669_);
v_snd_670_ = lean_ctor_get(v_head_667_, 1);
lean_inc(v_snd_670_);
lean_dec(v_head_667_);
lean_inc_ref(v_inst_664_);
v___x_671_ = l_Std_Internal_List_insertEntry___redArg(v_inst_664_, v_fst_669_, v_snd_670_, v_l_665_);
v_l_665_ = v___x_671_;
v_toInsert_666_ = v_tail_668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_inst_675_, lean_object* v_l_676_, lean_object* v_toInsert_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_Internal_List_insertList___redArg(v_inst_675_, v_l_676_, v_toInsert_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew___redArg(lean_object* v_inst_679_, lean_object* v_l_680_, lean_object* v_toInsert_681_){
_start:
{
if (lean_obj_tag(v_toInsert_681_) == 0)
{
lean_dec_ref(v_inst_679_);
return v_l_680_;
}
else
{
lean_object* v_head_682_; lean_object* v_tail_683_; lean_object* v_fst_684_; lean_object* v_snd_685_; lean_object* v___x_686_; 
v_head_682_ = lean_ctor_get(v_toInsert_681_, 0);
lean_inc(v_head_682_);
v_tail_683_ = lean_ctor_get(v_toInsert_681_, 1);
lean_inc(v_tail_683_);
lean_dec_ref(v_toInsert_681_);
v_fst_684_ = lean_ctor_get(v_head_682_, 0);
lean_inc(v_fst_684_);
v_snd_685_ = lean_ctor_get(v_head_682_, 1);
lean_inc(v_snd_685_);
lean_dec(v_head_682_);
lean_inc_ref(v_inst_679_);
v___x_686_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_679_, v_fst_684_, v_snd_685_, v_l_680_);
v_l_680_ = v___x_686_;
v_toInsert_681_ = v_tail_683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_inst_690_, lean_object* v_l_691_, lean_object* v_toInsert_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_Internal_List_insertListIfNew___redArg(v_inst_690_, v_l_691_, v_toInsert_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList___redArg(lean_object* v_inst_694_, lean_object* v_l_u2081_695_, lean_object* v_l_u2082_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = l_List_lengthTR___redArg(v_l_u2081_695_);
v___x_698_ = l_List_lengthTR___redArg(v_l_u2082_696_);
v___x_699_ = lean_nat_dec_le(v___x_697_, v___x_698_);
lean_dec(v___x_698_);
lean_dec(v___x_697_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_Internal_List_insertList___redArg(v_inst_694_, v_l_u2081_695_, v_l_u2082_696_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = l_Std_Internal_List_insertListIfNew___redArg(v_inst_694_, v_l_u2082_696_, v_l_u2081_695_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList(lean_object* v_00_u03b1_702_, lean_object* v_00_u03b2_703_, lean_object* v_inst_704_, lean_object* v_l_u2081_705_, lean_object* v_l_u2082_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_Internal_List_insertSmallerList___redArg(v_inst_704_, v_l_u2081_705_, v_l_u2082_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma___redArg(lean_object* v_p_708_){
_start:
{
lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
v_fst_709_ = lean_ctor_get(v_p_708_, 0);
v_snd_710_ = lean_ctor_get(v_p_708_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_p_708_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v_p_708_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_inc(v_fst_709_);
lean_dec(v_p_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_snd_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma(lean_object* v_00_u03b1_718_, lean_object* v_00_u03b2_719_, lean_object* v_p_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Std_Internal_List_Prod_toSigma___redArg(v_p_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst___redArg(lean_object* v_inst_723_, lean_object* v_l_724_, lean_object* v_toInsert_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = ((lean_object*)(l_Std_Internal_List_insertListConst___redArg___closed__0));
v___x_727_ = lean_box(0);
v___x_728_ = l_List_mapTR_loop___redArg(v___x_726_, v_toInsert_725_, v___x_727_);
v___x_729_ = l_Std_Internal_List_insertList___redArg(v_inst_723_, v_l_724_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst(lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_inst_732_, lean_object* v_l_733_, lean_object* v_toInsert_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_Internal_List_insertListConst___redArg(v_inst_732_, v_l_733_, v_toInsert_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit___redArg(lean_object* v_inst_736_, lean_object* v_l_737_, lean_object* v_toInsert_738_){
_start:
{
if (lean_obj_tag(v_toInsert_738_) == 0)
{
lean_dec_ref(v_inst_736_);
return v_l_737_;
}
else
{
lean_object* v_head_739_; lean_object* v_tail_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_head_739_ = lean_ctor_get(v_toInsert_738_, 0);
lean_inc(v_head_739_);
v_tail_740_ = lean_ctor_get(v_toInsert_738_, 1);
lean_inc(v_tail_740_);
lean_dec_ref(v_toInsert_738_);
v___x_741_ = lean_box(0);
lean_inc_ref(v_inst_736_);
v___x_742_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_736_, v_head_739_, v___x_741_, v_l_737_);
v_l_737_ = v___x_742_;
v_toInsert_738_ = v_tail_740_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit(lean_object* v_00_u03b1_744_, lean_object* v_inst_745_, lean_object* v_l_746_, lean_object* v_toInsert_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_Internal_List_insertListIfNewUnit___redArg(v_inst_745_, v_l_746_, v_toInsert_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(lean_object* v_toInsert_749_, lean_object* v_h__1_750_, lean_object* v_h__2_751_){
_start:
{
if (lean_obj_tag(v_toInsert_749_) == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec(v_h__2_751_);
v___x_752_ = lean_box(0);
v___x_753_ = lean_apply_1(v_h__1_750_, v___x_752_);
return v___x_753_;
}
else
{
lean_object* v_head_754_; lean_object* v_tail_755_; lean_object* v___x_756_; 
lean_dec(v_h__1_750_);
v_head_754_ = lean_ctor_get(v_toInsert_749_, 0);
lean_inc(v_head_754_);
v_tail_755_ = lean_ctor_get(v_toInsert_749_, 1);
lean_inc(v_tail_755_);
lean_dec_ref(v_toInsert_749_);
v___x_756_ = lean_apply_2(v_h__2_751_, v_head_754_, v_tail_755_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object* v_00_u03b1_757_, lean_object* v_motive_758_, lean_object* v_toInsert_759_, lean_object* v_h__1_760_, lean_object* v_h__2_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(v_toInsert_759_, v_h__1_760_, v_h__2_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey___redArg(lean_object* v_inst_763_, lean_object* v_k_764_, lean_object* v_f_765_, lean_object* v_l_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_inc(v_l_766_);
lean_inc(v_k_764_);
lean_inc_ref(v_inst_763_);
v___x_767_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_763_, v_k_764_, v_l_766_);
v___x_768_ = lean_apply_1(v_f_765_, v___x_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_Internal_List_eraseKey___redArg(v_inst_763_, v_k_764_, v_l_766_);
return v___x_769_;
}
else
{
lean_object* v_val_770_; lean_object* v___x_771_; 
v_val_770_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_770_);
lean_dec_ref(v___x_768_);
v___x_771_ = l_Std_Internal_List_insertEntry___redArg(v_inst_763_, v_k_764_, v_val_770_, v_l_766_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_k_776_, lean_object* v_f_777_, lean_object* v_l_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_Internal_List_alterKey___redArg(v_inst_774_, v_k_776_, v_f_777_, v_l_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object* v_x_780_, lean_object* v_h__1_781_, lean_object* v_h__2_782_){
_start:
{
if (lean_obj_tag(v_x_780_) == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec(v_h__2_782_);
v___x_783_ = lean_box(0);
v___x_784_ = lean_apply_1(v_h__1_781_, v___x_783_);
return v___x_784_;
}
else
{
lean_object* v_val_785_; lean_object* v___x_786_; 
lean_dec(v_h__1_781_);
v_val_785_ = lean_ctor_get(v_x_780_, 0);
lean_inc(v_val_785_);
lean_dec_ref(v_x_780_);
v___x_786_ = lean_apply_1(v_h__2_782_, v_val_785_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* v_00_u03b1_787_, lean_object* v_00_u03b2_788_, lean_object* v_k_789_, lean_object* v_motive_790_, lean_object* v_x_791_, lean_object* v_h__1_792_, lean_object* v_h__2_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___redArg(v_x_791_, v_h__1_792_, v_h__2_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_k_797_, lean_object* v_motive_798_, lean_object* v_x_799_, lean_object* v_h__1_800_, lean_object* v_h__2_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_795_, v_00_u03b2_796_, v_k_797_, v_motive_798_, v_x_799_, v_h__1_800_, v_h__2_801_);
lean_dec(v_k_797_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_803_, lean_object* v_h__1_804_, lean_object* v_h__2_805_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v_h__2_805_);
v___x_806_ = lean_box(0);
v___x_807_ = lean_apply_1(v_h__1_804_, v___x_806_);
return v___x_807_;
}
else
{
lean_object* v_val_808_; lean_object* v___x_809_; 
lean_dec(v_h__1_804_);
v_val_808_ = lean_ctor_get(v_x_803_, 0);
lean_inc(v_val_808_);
lean_dec_ref(v_x_803_);
v___x_809_ = lean_apply_1(v_h__2_805_, v_val_808_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_k_812_, lean_object* v_motive_813_, lean_object* v_x_814_, lean_object* v_h__1_815_, lean_object* v_h__2_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(v_x_814_, v_h__1_815_, v_h__2_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_818_, lean_object* v_00_u03b2_819_, lean_object* v_k_820_, lean_object* v_motive_821_, lean_object* v_x_822_, lean_object* v_h__1_823_, lean_object* v_h__2_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_818_, v_00_u03b2_819_, v_k_820_, v_motive_821_, v_x_822_, v_h__1_823_, v_h__2_824_);
lean_dec(v_k_820_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey___redArg(lean_object* v_inst_826_, lean_object* v_k_827_, lean_object* v_f_828_, lean_object* v_l_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_inc(v_l_829_);
lean_inc(v_k_827_);
lean_inc_ref(v_inst_826_);
v___x_830_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_826_, v_k_827_, v_l_829_);
v___x_831_ = lean_apply_1(v_f_828_, v___x_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_Internal_List_eraseKey___redArg(v_inst_826_, v_k_827_, v_l_829_);
return v___x_832_;
}
else
{
lean_object* v_val_833_; lean_object* v___x_834_; 
v_val_833_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_val_833_);
lean_dec_ref(v___x_831_);
v___x_834_ = l_Std_Internal_List_insertEntry___redArg(v_inst_826_, v_k_827_, v_val_833_, v_l_829_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey(lean_object* v_00_u03b1_835_, lean_object* v_00_u03b2_836_, lean_object* v_inst_837_, lean_object* v_k_838_, lean_object* v_f_839_, lean_object* v_l_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_Internal_List_Const_alterKey___redArg(v_inst_837_, v_k_838_, v_f_839_, v_l_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object* v_x_842_, lean_object* v_h__1_843_, lean_object* v_h__2_844_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v_h__2_844_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_apply_1(v_h__1_843_, v___x_845_);
return v___x_846_;
}
else
{
lean_object* v_val_847_; lean_object* v___x_848_; 
lean_dec(v_h__1_843_);
v_val_847_ = lean_ctor_get(v_x_842_, 0);
lean_inc(v_val_847_);
lean_dec_ref(v_x_842_);
v___x_848_ = lean_apply_1(v_h__2_844_, v_val_847_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* v_00_u03b2_849_, lean_object* v_motive_850_, lean_object* v_x_851_, lean_object* v_h__1_852_, lean_object* v_h__2_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(v_x_851_, v_h__1_852_, v_h__2_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_855_, lean_object* v_h__1_856_, lean_object* v_h__2_857_){
_start:
{
if (lean_obj_tag(v_x_855_) == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_h__2_857_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_apply_1(v_h__1_856_, v___x_858_);
return v___x_859_;
}
else
{
lean_object* v_val_860_; lean_object* v___x_861_; 
lean_dec(v_h__1_856_);
v_val_860_ = lean_ctor_get(v_x_855_, 0);
lean_inc(v_val_860_);
lean_dec_ref(v_x_855_);
v___x_861_ = lean_apply_1(v_h__2_857_, v_val_860_);
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b2_862_, lean_object* v_motive_863_, lean_object* v_x_864_, lean_object* v_h__1_865_, lean_object* v_h__2_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(v_x_864_, v_h__1_865_, v_h__2_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey___redArg(lean_object* v_inst_868_, lean_object* v_k_869_, lean_object* v_f_870_, lean_object* v_l_871_){
_start:
{
lean_object* v___x_872_; 
lean_inc(v_l_871_);
lean_inc(v_k_869_);
lean_inc_ref(v_inst_868_);
v___x_872_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_868_, v_k_869_, v_l_871_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_dec(v_f_870_);
lean_dec(v_k_869_);
lean_dec_ref(v_inst_868_);
return v_l_871_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_val_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_val_873_);
lean_dec_ref(v___x_872_);
v___x_874_ = lean_apply_1(v_f_870_, v_val_873_);
v___x_875_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_868_, v_k_869_, v___x_874_, v_l_871_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey(lean_object* v_00_u03b1_876_, lean_object* v_00_u03b2_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_k_880_, lean_object* v_f_881_, lean_object* v_l_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Std_Internal_List_modifyKey___redArg(v_inst_878_, v_k_880_, v_f_881_, v_l_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey___redArg(lean_object* v_inst_884_, lean_object* v_k_885_, lean_object* v_f_886_, lean_object* v_l_887_){
_start:
{
lean_object* v___x_888_; 
lean_inc(v_l_887_);
lean_inc(v_k_885_);
lean_inc_ref(v_inst_884_);
v___x_888_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_884_, v_k_885_, v_l_887_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_dec(v_f_886_);
lean_dec(v_k_885_);
lean_dec_ref(v_inst_884_);
return v_l_887_;
}
else
{
lean_object* v_val_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_val_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_val_889_);
lean_dec_ref(v___x_888_);
v___x_890_ = lean_apply_1(v_f_886_, v_val_889_);
v___x_891_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_884_, v_k_885_, v___x_890_, v_l_887_);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey(lean_object* v_00_u03b1_892_, lean_object* v_00_u03b2_893_, lean_object* v_inst_894_, lean_object* v_k_895_, lean_object* v_f_896_, lean_object* v_l_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_Internal_List_Const_modifyKey___redArg(v_inst_894_, v_k_895_, v_f_896_, v_l_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_899_, lean_object* v_h__1_900_, lean_object* v_h__2_901_){
_start:
{
if (lean_obj_tag(v_x_899_) == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v_h__1_900_);
v___x_902_ = lean_box(0);
v___x_903_ = lean_apply_1(v_h__2_901_, v___x_902_);
return v___x_903_;
}
else
{
lean_object* v_val_904_; lean_object* v___x_905_; 
lean_dec(v_h__2_901_);
v_val_904_ = lean_ctor_get(v_x_899_, 0);
lean_inc(v_val_904_);
lean_dec_ref(v_x_899_);
v___x_905_ = lean_apply_1(v_h__1_900_, v_val_904_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_906_, lean_object* v_motive_907_, lean_object* v_x_908_, lean_object* v_h__1_909_, lean_object* v_h__2_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___redArg(v_x_908_, v_h__1_909_, v_h__2_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList___redArg(lean_object* v_inst_912_, lean_object* v_l_913_, lean_object* v_toErase_914_){
_start:
{
if (lean_obj_tag(v_toErase_914_) == 0)
{
lean_dec_ref(v_inst_912_);
return v_l_913_;
}
else
{
lean_object* v_head_915_; lean_object* v_tail_916_; lean_object* v___x_917_; 
v_head_915_ = lean_ctor_get(v_toErase_914_, 0);
lean_inc(v_head_915_);
v_tail_916_ = lean_ctor_get(v_toErase_914_, 1);
lean_inc(v_tail_916_);
lean_dec_ref(v_toErase_914_);
lean_inc_ref(v_inst_912_);
v___x_917_ = l_Std_Internal_List_eraseKey___redArg(v_inst_912_, v_head_915_, v_l_913_);
v_l_913_ = v___x_917_;
v_toErase_914_ = v_tail_916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList(lean_object* v_00_u03b1_919_, lean_object* v_00_u03b2_920_, lean_object* v_inst_921_, lean_object* v_l_922_, lean_object* v_toErase_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_Internal_List_eraseList___redArg(v_inst_921_, v_l_922_, v_toErase_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_925_, lean_object* v_h__1_926_, lean_object* v_h__2_927_){
_start:
{
if (lean_obj_tag(v_opt_925_) == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec(v_h__1_926_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_apply_1(v_h__2_927_, v___x_928_);
return v___x_929_;
}
else
{
lean_object* v_val_930_; lean_object* v___x_931_; 
lean_dec(v_h__2_927_);
v_val_930_ = lean_ctor_get(v_opt_925_, 0);
lean_inc(v_val_930_);
lean_dec_ref(v_opt_925_);
v___x_931_ = lean_apply_1(v_h__1_926_, v_val_930_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_932_, lean_object* v_motive_933_, lean_object* v_opt_934_, lean_object* v_h__1_935_, lean_object* v_h__2_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___redArg(v_opt_934_, v_h__1_935_, v_h__2_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(lean_object* v_00_u03b1_938_, lean_object* v_00_u03b2_939_, lean_object* v_inst_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lean_box(0);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___boxed(lean_object* v_00_u03b1_942_, lean_object* v_00_u03b2_943_, lean_object* v_inst_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(v_00_u03b1_942_, v_00_u03b2_943_, v_inst_944_);
lean_dec_ref(v_inst_944_);
return v_res_945_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(lean_object* v_inst_946_, lean_object* v_a_947_, lean_object* v_b_948_){
_start:
{
lean_object* v_fst_949_; lean_object* v_fst_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_fst_949_ = lean_ctor_get(v_a_947_, 0);
lean_inc(v_fst_949_);
lean_dec_ref(v_a_947_);
v_fst_950_ = lean_ctor_get(v_b_948_, 0);
lean_inc(v_fst_950_);
lean_dec_ref(v_b_948_);
v___x_951_ = lean_apply_2(v_inst_946_, v_fst_949_, v_fst_950_);
v___x_952_ = lean_unbox(v___x_951_);
if (v___x_952_ == 2)
{
uint8_t v___x_953_; 
v___x_953_ = 0;
return v___x_953_;
}
else
{
uint8_t v___x_954_; 
v___x_954_ = 1;
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg___boxed(lean_object* v_inst_955_, lean_object* v_a_956_, lean_object* v_b_957_){
_start:
{
uint8_t v_res_958_; lean_object* v_r_959_; 
v_res_958_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_955_, v_a_956_, v_b_957_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(lean_object* v_00_u03b1_960_, lean_object* v_00_u03b2_961_, lean_object* v_inst_962_, lean_object* v_a_963_, lean_object* v_b_964_){
_start:
{
uint8_t v___x_965_; 
v___x_965_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_962_, v_a_963_, v_b_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___boxed(lean_object* v_00_u03b1_966_, lean_object* v_00_u03b2_967_, lean_object* v_inst_968_, lean_object* v_a_969_, lean_object* v_b_970_){
_start:
{
uint8_t v_res_971_; lean_object* v_r_972_; 
v_res_971_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(v_00_u03b1_966_, v_00_u03b2_967_, v_inst_968_, v_a_969_, v_b_970_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0(lean_object* v_inst_973_, lean_object* v_a_974_, lean_object* v_b_975_){
_start:
{
lean_object* v_fst_976_; lean_object* v_fst_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_fst_976_ = lean_ctor_get(v_a_974_, 0);
v_fst_977_ = lean_ctor_get(v_b_975_, 0);
lean_inc(v_fst_977_);
lean_inc(v_fst_976_);
v___x_978_ = lean_apply_2(v_inst_973_, v_fst_976_, v_fst_977_);
v___x_979_ = lean_unbox(v___x_978_);
if (v___x_979_ == 2)
{
lean_dec_ref(v_a_974_);
return v_b_975_;
}
else
{
lean_dec_ref(v_b_975_);
return v_a_974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg(lean_object* v_inst_980_){
_start:
{
lean_object* v___f_981_; 
v___f_981_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_981_, 0, v_inst_980_);
return v___f_981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd(lean_object* v_00_u03b1_982_, lean_object* v_00_u03b2_983_, lean_object* v_inst_984_){
_start:
{
lean_object* v___f_985_; 
v___f_985_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_985_, 0, v_inst_984_);
return v___f_985_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___redArg(lean_object* v_inst_986_, lean_object* v_xs_987_){
_start:
{
lean_object* v___f_988_; lean_object* v___x_989_; 
v___f_988_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_988_, 0, v_inst_986_);
v___x_989_ = l_List_min_x3f___redArg(v___f_988_, v_xs_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f(lean_object* v_00_u03b1_990_, lean_object* v_00_u03b2_991_, lean_object* v_inst_992_, lean_object* v_xs_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_992_, v_xs_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___redArg(lean_object* v_inst_995_, lean_object* v_xs_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_995_, v_xs_996_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; 
v___x_998_ = lean_box(0);
return v___x_998_;
}
else
{
lean_object* v_val_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1007_; 
v_val_999_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1001_ = v___x_997_;
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_val_999_);
lean_dec(v___x_997_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_fst_1003_; lean_object* v___x_1005_; 
v_fst_1003_ = lean_ctor_get(v_val_999_, 0);
lean_inc(v_fst_1003_);
lean_dec(v_val_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_fst_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_fst_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f(lean_object* v_00_u03b1_1008_, lean_object* v_00_u03b2_1009_, lean_object* v_inst_1010_, lean_object* v_xs_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1010_, v_xs_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___redArg(lean_object* v_x_1013_, lean_object* v_h__1_1014_, lean_object* v_h__2_1015_){
_start:
{
if (lean_obj_tag(v_x_1013_) == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v_h__2_1015_);
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_apply_1(v_h__1_1014_, v___x_1016_);
return v___x_1017_;
}
else
{
lean_object* v_val_1018_; lean_object* v___x_1019_; 
lean_dec(v_h__1_1014_);
v_val_1018_ = lean_ctor_get(v_x_1013_, 0);
lean_inc(v_val_1018_);
lean_dec_ref(v_x_1013_);
v___x_1019_ = lean_apply_1(v_h__2_1015_, v_val_1018_);
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_motive_1022_, lean_object* v_x_1023_, lean_object* v_h__1_1024_, lean_object* v_h__2_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___redArg(v_x_1023_, v_h__1_1024_, v_h__2_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_1027_, lean_object* v_h__1_1028_, lean_object* v_h__2_1029_){
_start:
{
if (lean_obj_tag(v_x_1027_) == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec(v_h__2_1029_);
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_apply_1(v_h__1_1028_, v___x_1030_);
return v___x_1031_;
}
else
{
lean_object* v_head_1032_; lean_object* v_tail_1033_; lean_object* v___x_1034_; 
lean_dec(v_h__1_1028_);
v_head_1032_ = lean_ctor_get(v_x_1027_, 0);
lean_inc(v_head_1032_);
v_tail_1033_ = lean_ctor_get(v_x_1027_, 1);
lean_inc(v_tail_1033_);
lean_dec_ref(v_x_1027_);
v___x_1034_ = lean_apply_2(v_h__2_1029_, v_head_1032_, v_tail_1033_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_1035_, lean_object* v_motive_1036_, lean_object* v_x_1037_, lean_object* v_h__1_1038_, lean_object* v_h__2_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___redArg(v_x_1037_, v_h__1_1038_, v_h__2_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter___redArg(lean_object* v_x_1041_, lean_object* v_h__1_1042_, lean_object* v_h__2_1043_){
_start:
{
if (lean_obj_tag(v_x_1041_) == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec(v_h__2_1043_);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_apply_1(v_h__1_1042_, v___x_1044_);
return v___x_1045_;
}
else
{
lean_object* v_val_1046_; lean_object* v___x_1047_; 
lean_dec(v_h__1_1042_);
v_val_1046_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_val_1046_);
lean_dec_ref(v_x_1041_);
v___x_1047_ = lean_apply_1(v_h__2_1043_, v_val_1046_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter(lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_motive_1050_, lean_object* v_x_1051_, lean_object* v_h__1_1052_, lean_object* v_h__2_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter___redArg(v_x_1051_, v_h__1_1052_, v_h__2_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___redArg(lean_object* v_inst_1055_, lean_object* v_xs_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v_val_1058_; 
v___x_1057_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1055_, v_xs_1056_);
v_val_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_val_1058_);
lean_dec(v___x_1057_);
return v_val_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey(lean_object* v_00_u03b1_1059_, lean_object* v_00_u03b2_1060_, lean_object* v_inst_1061_, lean_object* v_xs_1062_, lean_object* v_h_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_Internal_List_minKey___redArg(v_inst_1061_, v_xs_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___redArg(lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_xs_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1065_, v_xs_1067_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_1070_ = l_panic___redArg(v_inst_1066_, v___x_1069_);
return v___x_1070_;
}
else
{
lean_object* v_val_1071_; 
lean_dec(v_inst_1066_);
v_val_1071_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_val_1071_);
lean_dec_ref(v___x_1068_);
return v_val_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21(lean_object* v_00_u03b1_1072_, lean_object* v_00_u03b2_1073_, lean_object* v_inst_1074_, lean_object* v_inst_1075_, lean_object* v_xs_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_1074_, v_inst_1075_, v_xs_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg(lean_object* v_inst_1078_, lean_object* v_xs_1079_, lean_object* v_fallback_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1078_, v_xs_1079_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_inc(v_fallback_1080_);
return v_fallback_1080_;
}
else
{
lean_object* v_val_1082_; 
v_val_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_val_1082_);
lean_dec_ref(v___x_1081_);
return v_val_1082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg___boxed(lean_object* v_inst_1083_, lean_object* v_xs_1084_, lean_object* v_fallback_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Std_Internal_List_minKeyD___redArg(v_inst_1083_, v_xs_1084_, v_fallback_1085_);
lean_dec(v_fallback_1085_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD(lean_object* v_00_u03b1_1087_, lean_object* v_00_u03b2_1088_, lean_object* v_inst_1089_, lean_object* v_xs_1090_, lean_object* v_fallback_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Std_Internal_List_minKeyD___redArg(v_inst_1089_, v_xs_1090_, v_fallback_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_00_u03b2_1094_, lean_object* v_inst_1095_, lean_object* v_xs_1096_, lean_object* v_fallback_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_Internal_List_minKeyD(v_00_u03b1_1093_, v_00_u03b2_1094_, v_inst_1095_, v_xs_1096_, v_fallback_1097_);
lean_dec(v_fallback_1097_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f___redArg(lean_object* v_inst_1099_, lean_object* v_xs_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; 
v___f_1101_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1101_, 0, v_inst_1099_);
v___x_1102_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1101_, v_xs_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f(lean_object* v_00_u03b1_1103_, lean_object* v_00_u03b2_1104_, lean_object* v_inst_1105_, lean_object* v_xs_1106_){
_start:
{
lean_object* v___f_1107_; lean_object* v___x_1108_; 
v___f_1107_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1107_, 0, v_inst_1105_);
v___x_1108_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1107_, v_xs_1106_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey___redArg(lean_object* v_inst_1109_, lean_object* v_xs_1110_){
_start:
{
lean_object* v___f_1111_; lean_object* v___x_1112_; 
v___f_1111_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1111_, 0, v_inst_1109_);
v___x_1112_ = l_Std_Internal_List_minKey___redArg(v___f_1111_, v_xs_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey(lean_object* v_00_u03b1_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_inst_1115_, lean_object* v_xs_1116_, lean_object* v_h_1117_){
_start:
{
lean_object* v___f_1118_; lean_object* v___x_1119_; 
v___f_1118_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1118_, 0, v_inst_1115_);
v___x_1119_ = l_Std_Internal_List_minKey___redArg(v___f_1118_, v_xs_1116_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg(lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_xs_1122_){
_start:
{
lean_object* v___f_1123_; lean_object* v___x_1124_; 
v___f_1123_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1123_, 0, v_inst_1120_);
v___x_1124_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1123_, v_xs_1122_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_1126_ = l_panic___redArg(v_inst_1121_, v___x_1125_);
return v___x_1126_;
}
else
{
lean_object* v_val_1127_; 
lean_dec(v_inst_1121_);
v_val_1127_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_val_1127_);
lean_dec_ref(v___x_1124_);
return v_val_1127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21(lean_object* v_00_u03b1_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_xs_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_1130_, v_inst_1131_, v_xs_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg(lean_object* v_inst_1134_, lean_object* v_xs_1135_, lean_object* v_fallback_1136_){
_start:
{
lean_object* v___f_1137_; lean_object* v___x_1138_; 
v___f_1137_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1137_, 0, v_inst_1134_);
v___x_1138_ = l_Std_Internal_List_minKeyD___redArg(v___f_1137_, v_xs_1135_, v_fallback_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg___boxed(lean_object* v_inst_1139_, lean_object* v_xs_1140_, lean_object* v_fallback_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_Internal_List_maxKeyD___redArg(v_inst_1139_, v_xs_1140_, v_fallback_1141_);
lean_dec(v_fallback_1141_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD(lean_object* v_00_u03b1_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_inst_1145_, lean_object* v_xs_1146_, lean_object* v_fallback_1147_){
_start:
{
lean_object* v___f_1148_; lean_object* v___x_1149_; 
v___f_1148_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1148_, 0, v_inst_1145_);
v___x_1149_ = l_Std_Internal_List_minKeyD___redArg(v___f_1148_, v_xs_1146_, v_fallback_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___boxed(lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_inst_1152_, lean_object* v_xs_1153_, lean_object* v_fallback_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_Internal_List_maxKeyD(v_00_u03b1_1150_, v_00_u03b2_1151_, v_inst_1152_, v_xs_1153_, v_fallback_1154_);
lean_dec(v_fallback_1154_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn___redArg(lean_object* v_inst_1156_, lean_object* v_l_1157_, lean_object* v_sofar_1158_, lean_object* v_k_1159_){
_start:
{
lean_object* v___x_1160_; 
lean_inc_ref(v_inst_1156_);
v___x_1160_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_1156_, v_k_1159_, v_l_1157_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_dec_ref(v_inst_1156_);
return v_sofar_1158_;
}
else
{
lean_object* v_val_1161_; lean_object* v_fst_1162_; lean_object* v_snd_1163_; lean_object* v___x_1164_; 
v_val_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_val_1161_);
lean_dec_ref(v___x_1160_);
v_fst_1162_ = lean_ctor_get(v_val_1161_, 0);
lean_inc(v_fst_1162_);
v_snd_1163_ = lean_ctor_get(v_val_1161_, 1);
lean_inc(v_snd_1163_);
lean_dec(v_val_1161_);
v___x_1164_ = l_Std_Internal_List_insertEntry___redArg(v_inst_1156_, v_fst_1162_, v_snd_1163_, v_sofar_1158_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn(lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_inst_1167_, lean_object* v_l_1168_, lean_object* v_sofar_1169_, lean_object* v_k_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Std_Internal_List_interSmallerFn___redArg(v_inst_1167_, v_l_1168_, v_sofar_1169_, v_k_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_1172_, lean_object* v_h__1_1173_, lean_object* v_h__2_1174_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v_h__1_1173_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_apply_1(v_h__2_1174_, v___x_1175_);
return v___x_1176_;
}
else
{
lean_object* v_val_1177_; lean_object* v___x_1178_; 
lean_dec(v_h__2_1174_);
v_val_1177_ = lean_ctor_get(v_x_1172_, 0);
lean_inc(v_val_1177_);
lean_dec_ref(v_x_1172_);
v___x_1178_ = lean_apply_1(v_h__1_1173_, v_val_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_1179_, lean_object* v_00_u03b2_1180_, lean_object* v_motive_1181_, lean_object* v_x_1182_, lean_object* v_h__1_1183_, lean_object* v_h__2_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(v_x_1182_, v_h__1_1183_, v_h__2_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg___lam__0(lean_object* v_inst_1186_, lean_object* v_l_u2081_1187_, lean_object* v_sofar_1188_, lean_object* v_kv_1189_){
_start:
{
lean_object* v_fst_1190_; lean_object* v___x_1191_; 
v_fst_1190_ = lean_ctor_get(v_kv_1189_, 0);
lean_inc(v_fst_1190_);
lean_dec_ref(v_kv_1189_);
v___x_1191_ = l_Std_Internal_List_interSmallerFn___redArg(v_inst_1186_, v_l_u2081_1187_, v_sofar_1188_, v_fst_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg(lean_object* v_inst_1192_, lean_object* v_l_u2081_1193_, lean_object* v_l_u2082_1194_){
_start:
{
lean_object* v___f_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___f_1195_ = lean_alloc_closure((void*)(l_Std_Internal_List_interSmaller___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1195_, 0, v_inst_1192_);
lean_closure_set(v___f_1195_, 1, v_l_u2081_1193_);
v___x_1196_ = lean_box(0);
v___x_1197_ = l_List_foldl___redArg(v___f_1195_, v___x_1196_, v_l_u2082_1194_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_inst_1200_, lean_object* v_l_u2081_1201_, lean_object* v_l_u2082_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Std_Internal_List_interSmaller___redArg(v_inst_1200_, v_l_u2081_1201_, v_l_u2082_1202_);
return v___x_1203_;
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
