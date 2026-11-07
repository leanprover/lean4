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
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___redArg___boxed(lean_object*);
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
lean_dec_ref_known(v_x_3_, 2);
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
lean_dec_ref_known(v_x_21_, 2);
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
lean_dec_ref_known(v_x_59_, 2);
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
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f___redArg(lean_object* v_inst_87_, lean_object* v_a_88_, lean_object* v_x_89_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v___x_90_; 
lean_dec(v_a_88_);
lean_dec_ref(v_inst_87_);
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v_head_91_; lean_object* v_tail_92_; lean_object* v_fst_93_; lean_object* v_snd_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v_head_91_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_head_91_);
v_tail_92_ = lean_ctor_get(v_x_89_, 1);
lean_inc(v_tail_92_);
lean_dec_ref_known(v_x_89_, 2);
v_fst_93_ = lean_ctor_get(v_head_91_, 0);
lean_inc(v_fst_93_);
v_snd_94_ = lean_ctor_get(v_head_91_, 1);
lean_inc(v_snd_94_);
lean_dec(v_head_91_);
lean_inc_ref(v_inst_87_);
lean_inc(v_a_88_);
v___x_95_ = lean_apply_2(v_inst_87_, v_fst_93_, v_a_88_);
v___x_96_ = lean_unbox(v___x_95_);
if (v___x_96_ == 0)
{
lean_dec(v_snd_94_);
v_x_89_ = v_tail_92_;
goto _start;
}
else
{
lean_object* v___x_98_; 
lean_dec(v_tail_92_);
lean_dec(v_a_88_);
lean_dec_ref(v_inst_87_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v_snd_94_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_inst_101_, lean_object* v_a_102_, lean_object* v_x_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_101_, v_a_102_, v_x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f___redArg(lean_object* v_inst_105_, lean_object* v_a_106_, lean_object* v_x_107_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v___x_108_; 
lean_dec(v_a_106_);
lean_dec_ref(v_inst_105_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v_head_109_; lean_object* v_tail_110_; lean_object* v_fst_111_; lean_object* v_snd_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_head_109_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_head_109_);
v_tail_110_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_tail_110_);
lean_dec_ref_known(v_x_107_, 2);
v_fst_111_ = lean_ctor_get(v_head_109_, 0);
lean_inc(v_fst_111_);
v_snd_112_ = lean_ctor_get(v_head_109_, 1);
lean_inc(v_snd_112_);
lean_dec(v_head_109_);
lean_inc_ref(v_inst_105_);
lean_inc(v_a_106_);
v___x_113_ = lean_apply_2(v_inst_105_, v_fst_111_, v_a_106_);
v___x_114_ = lean_unbox(v___x_113_);
if (v___x_114_ == 0)
{
lean_dec(v_snd_112_);
v_x_107_ = v_tail_110_;
goto _start;
}
else
{
lean_object* v___x_116_; 
lean_dec(v_tail_110_);
lean_dec(v_a_106_);
lean_dec_ref(v_inst_105_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_snd_112_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_a_121_, lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_119_, v_a_121_, v_x_122_);
return v___x_123_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg___lam__0(lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_l_u2082_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_fst_128_; lean_object* v_snd_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_fst_128_ = lean_ctor_get(v_x_127_, 0);
lean_inc_n(v_fst_128_, 2);
v_snd_129_ = lean_ctor_get(v_x_127_, 1);
lean_inc(v_snd_129_);
lean_dec_ref(v_x_127_);
v___x_130_ = lean_apply_1(v_inst_124_, v_fst_128_);
v___x_131_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_125_, v_fst_128_, v_l_u2082_126_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v_snd_129_);
v___x_133_ = l_instBEqOption_beq___redArg(v___x_130_, v___x_131_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___lam__0___boxed(lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_l_u2082_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Std_Internal_List_beqModel___redArg___lam__0(v_inst_134_, v_inst_135_, v_l_u2082_136_, v_x_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel___redArg(lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_l_u2081_142_, lean_object* v_l_u2082_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_144_ = l_List_lengthTR___redArg(v_l_u2081_142_);
v___x_145_ = l_List_lengthTR___redArg(v_l_u2082_143_);
v___x_146_ = lean_nat_dec_eq(v___x_144_, v___x_145_);
lean_dec(v___x_145_);
lean_dec(v___x_144_);
if (v___x_146_ == 0)
{
lean_dec(v_l_u2082_143_);
lean_dec(v_l_u2081_142_);
lean_dec_ref(v_inst_141_);
lean_dec_ref(v_inst_140_);
return v___x_146_;
}
else
{
lean_object* v___f_147_; uint8_t v___x_148_; 
v___f_147_ = lean_alloc_closure((void*)(l_Std_Internal_List_beqModel___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_147_, 0, v_inst_141_);
lean_closure_set(v___f_147_, 1, v_inst_140_);
lean_closure_set(v___f_147_, 2, v_l_u2082_143_);
v___x_148_ = l_List_all___redArg(v_l_u2081_142_, v___f_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___boxed(lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_l_u2081_151_, lean_object* v_l_u2082_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Std_Internal_List_beqModel___redArg(v_inst_149_, v_inst_150_, v_l_u2081_151_, v_l_u2082_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_beqModel(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_l_u2081_160_, lean_object* v_l_u2082_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = l_Std_Internal_List_beqModel___redArg(v_inst_157_, v_inst_159_, v_l_u2081_160_, v_l_u2082_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___boxed(lean_object* v_00_u03b1_163_, lean_object* v_00_u03b2_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_l_u2081_168_, lean_object* v_l_u2082_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Std_Internal_List_beqModel(v_00_u03b1_163_, v_00_u03b2_164_, v_inst_165_, v_inst_166_, v_inst_167_, v_l_u2081_168_, v_l_u2082_169_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg___lam__0(lean_object* v_inst_172_, lean_object* v_l_u2082_173_, lean_object* v_inst_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_fst_176_ = lean_ctor_get(v_x_175_, 0);
lean_inc(v_fst_176_);
v_snd_177_ = lean_ctor_get(v_x_175_, 1);
lean_inc(v_snd_177_);
lean_dec_ref(v_x_175_);
v___x_178_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_172_, v_fst_176_, v_l_u2082_173_);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v_snd_177_);
v___x_180_ = l_instBEqOption_beq___redArg(v_inst_174_, v___x_178_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed(lean_object* v_inst_181_, lean_object* v_l_u2082_182_, lean_object* v_inst_183_, lean_object* v_x_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Std_Internal_List_Const_beqModel___redArg___lam__0(v_inst_181_, v_l_u2082_182_, v_inst_183_, v_x_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel___redArg(lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_l_u2081_189_, lean_object* v_l_u2082_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_191_ = l_List_lengthTR___redArg(v_l_u2081_189_);
v___x_192_ = l_List_lengthTR___redArg(v_l_u2082_190_);
v___x_193_ = lean_nat_dec_eq(v___x_191_, v___x_192_);
lean_dec(v___x_192_);
lean_dec(v___x_191_);
if (v___x_193_ == 0)
{
lean_dec(v_l_u2082_190_);
lean_dec(v_l_u2081_189_);
lean_dec_ref(v_inst_188_);
lean_dec_ref(v_inst_187_);
return v___x_193_;
}
else
{
lean_object* v___f_194_; uint8_t v___x_195_; 
v___f_194_ = lean_alloc_closure((void*)(l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_194_, 0, v_inst_187_);
lean_closure_set(v___f_194_, 1, v_l_u2082_190_);
lean_closure_set(v___f_194_, 2, v_inst_188_);
v___x_195_ = l_List_all___redArg(v_l_u2081_189_, v___f_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___boxed(lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_l_u2081_198_, lean_object* v_l_u2082_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_196_, v_inst_197_, v_l_u2081_198_, v_l_u2082_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_Const_beqModel(lean_object* v_00_u03b1_202_, lean_object* v_00_u03b2_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_l_u2081_206_, lean_object* v_l_u2082_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_204_, v_inst_205_, v_l_u2081_206_, v_l_u2082_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___boxed(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_l_u2081_213_, lean_object* v_l_u2082_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_Std_Internal_List_Const_beqModel(v_00_u03b1_209_, v_00_u03b2_210_, v_inst_211_, v_inst_212_, v_l_u2081_213_, v_l_u2082_214_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v___x_219_; 
lean_dec(v_x_218_);
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v_val_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_val_220_ = lean_ctor_get(v_x_217_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_217_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v_x_217_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_val_220_);
lean_dec(v_x_217_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_apply_2(v_x_218_, v_val_220_, lean_box(0));
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap(lean_object* v_00_u03b1_229_, lean_object* v_00_u03b2_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(v_x_231_, v_x_232_);
return v___x_233_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey___redArg(lean_object* v_inst_234_, lean_object* v_a_235_, lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_236_) == 0)
{
uint8_t v___x_237_; 
lean_dec(v_a_235_);
lean_dec_ref(v_inst_234_);
v___x_237_ = 0;
return v___x_237_;
}
else
{
lean_object* v_head_238_; lean_object* v_tail_239_; lean_object* v_fst_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_head_238_ = lean_ctor_get(v_x_236_, 0);
lean_inc(v_head_238_);
v_tail_239_ = lean_ctor_get(v_x_236_, 1);
lean_inc(v_tail_239_);
lean_dec_ref_known(v_x_236_, 2);
v_fst_240_ = lean_ctor_get(v_head_238_, 0);
lean_inc(v_fst_240_);
lean_dec(v_head_238_);
lean_inc_ref(v_inst_234_);
lean_inc(v_a_235_);
v___x_241_ = lean_apply_2(v_inst_234_, v_fst_240_, v_a_235_);
v___x_242_ = lean_unbox(v___x_241_);
if (v___x_242_ == 0)
{
v_x_236_ = v_tail_239_;
goto _start;
}
else
{
uint8_t v___x_244_; 
lean_dec(v_tail_239_);
lean_dec(v_a_235_);
lean_dec_ref(v_inst_234_);
v___x_244_ = lean_unbox(v___x_241_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___redArg___boxed(lean_object* v_inst_245_, lean_object* v_a_246_, lean_object* v_x_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Std_Internal_List_containsKey___redArg(v_inst_245_, v_a_246_, v_x_247_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey(lean_object* v_00_u03b1_250_, lean_object* v_00_u03b2_251_, lean_object* v_inst_252_, lean_object* v_a_253_, lean_object* v_x_254_){
_start:
{
uint8_t v___x_255_; 
v___x_255_ = l_Std_Internal_List_containsKey___redArg(v_inst_252_, v_a_253_, v_x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___boxed(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_inst_258_, lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_Internal_List_containsKey(v_00_u03b1_256_, v_00_u03b2_257_, v_inst_258_, v_a_259_, v_x_260_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry___redArg(lean_object* v_inst_263_, lean_object* v_a_264_, lean_object* v_l_265_){
_start:
{
lean_object* v___x_266_; lean_object* v_val_267_; 
v___x_266_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_263_, v_a_264_, v_l_265_);
v_val_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_val_267_);
lean_dec(v___x_266_);
return v_val_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry(lean_object* v_00_u03b1_268_, lean_object* v_00_u03b2_269_, lean_object* v_inst_270_, lean_object* v_a_271_, lean_object* v_l_272_, lean_object* v_h_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Std_Internal_List_getEntry___redArg(v_inst_270_, v_a_271_, v_l_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue___redArg(lean_object* v_inst_275_, lean_object* v_a_276_, lean_object* v_l_277_){
_start:
{
lean_object* v___x_278_; lean_object* v_val_279_; 
v___x_278_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_275_, v_a_276_, v_l_277_);
v_val_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_val_279_);
lean_dec(v___x_278_);
return v_val_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_inst_282_, lean_object* v_a_283_, lean_object* v_l_284_, lean_object* v_h_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_Internal_List_getValue___redArg(v_inst_282_, v_a_283_, v_l_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast___redArg(lean_object* v_inst_287_, lean_object* v_a_288_, lean_object* v_l_289_){
_start:
{
lean_object* v___x_290_; lean_object* v_val_291_; 
v___x_290_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_287_, v_a_288_, v_l_289_);
v_val_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_val_291_);
lean_dec(v___x_290_);
return v_val_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast(lean_object* v_00_u03b1_292_, lean_object* v_00_u03b2_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_a_296_, lean_object* v_l_297_, lean_object* v_h_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Std_Internal_List_getValueCast___redArg(v_inst_294_, v_a_296_, v_l_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg(lean_object* v_inst_300_, lean_object* v_a_301_, lean_object* v_l_302_, lean_object* v_fallback_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_300_, v_a_301_, v_l_302_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_inc(v_fallback_303_);
return v_fallback_303_;
}
else
{
lean_object* v_val_305_; 
v_val_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v___x_304_, 1);
return v_val_305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg___boxed(lean_object* v_inst_306_, lean_object* v_a_307_, lean_object* v_l_308_, lean_object* v_fallback_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Internal_List_getValueCastD___redArg(v_inst_306_, v_a_307_, v_l_308_, v_fallback_309_);
lean_dec(v_fallback_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_a_315_, lean_object* v_l_316_, lean_object* v_fallback_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_Internal_List_getValueCastD___redArg(v_inst_313_, v_a_315_, v_l_316_, v_fallback_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___boxed(lean_object* v_00_u03b1_319_, lean_object* v_00_u03b2_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_a_323_, lean_object* v_l_324_, lean_object* v_fallback_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_Internal_List_getValueCastD(v_00_u03b1_319_, v_00_u03b2_320_, v_inst_321_, v_inst_322_, v_a_323_, v_l_324_, v_fallback_325_);
lean_dec(v_fallback_325_);
return v_res_326_;
}
}
static lean_object* _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_330_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__2));
v___x_331_ = lean_unsigned_to_nat(14u);
v___x_332_ = lean_unsigned_to_nat(22u);
v___x_333_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__1));
v___x_334_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__0));
v___x_335_ = l_mkPanicMessageWithDecl(v___x_334_, v___x_333_, v___x_332_, v___x_331_, v___x_330_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___redArg(lean_object* v_inst_336_, lean_object* v_a_337_, lean_object* v_inst_338_, lean_object* v_l_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_336_, v_a_337_, v_l_339_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_342_ = l_panic___redArg(v_inst_338_, v___x_341_);
return v___x_342_;
}
else
{
lean_object* v_val_343_; 
v_val_343_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v___x_340_, 1);
return v_val_343_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___redArg___boxed(lean_object* v_inst_344_, lean_object* v_a_345_, lean_object* v_inst_346_, lean_object* v_l_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Internal_List_getValueCast_x21___redArg(v_inst_344_, v_a_345_, v_inst_346_, v_l_347_);
lean_dec(v_inst_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21(lean_object* v_00_u03b1_349_, lean_object* v_00_u03b2_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_a_353_, lean_object* v_inst_354_, lean_object* v_l_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_Internal_List_getValueCast_x21___redArg(v_inst_351_, v_a_353_, v_inst_354_, v_l_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___boxed(lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_a_361_, lean_object* v_inst_362_, lean_object* v_l_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_Internal_List_getValueCast_x21(v_00_u03b1_357_, v_00_u03b2_358_, v_inst_359_, v_inst_360_, v_a_361_, v_inst_362_, v_l_363_);
lean_dec(v_inst_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg(lean_object* v_inst_365_, lean_object* v_a_366_, lean_object* v_l_367_, lean_object* v_fallback_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_365_, v_a_366_, v_l_367_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_inc(v_fallback_368_);
return v_fallback_368_;
}
else
{
lean_object* v_val_370_; 
v_val_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v___x_369_, 1);
return v_val_370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg___boxed(lean_object* v_inst_371_, lean_object* v_a_372_, lean_object* v_l_373_, lean_object* v_fallback_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_Internal_List_getValueD___redArg(v_inst_371_, v_a_372_, v_l_373_, v_fallback_374_);
lean_dec(v_fallback_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v_inst_378_, lean_object* v_a_379_, lean_object* v_l_380_, lean_object* v_fallback_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_Internal_List_getValueD___redArg(v_inst_378_, v_a_379_, v_l_380_, v_fallback_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___boxed(lean_object* v_00_u03b1_383_, lean_object* v_00_u03b2_384_, lean_object* v_inst_385_, lean_object* v_a_386_, lean_object* v_l_387_, lean_object* v_fallback_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_Internal_List_getValueD(v_00_u03b1_383_, v_00_u03b2_384_, v_inst_385_, v_a_386_, v_l_387_, v_fallback_388_);
lean_dec(v_fallback_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg(lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_a_392_, lean_object* v_l_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_390_, v_a_392_, v_l_393_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_396_ = l_panic___redArg(v_inst_391_, v___x_395_);
return v___x_396_;
}
else
{
lean_object* v_val_397_; 
v_val_397_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v___x_394_, 1);
return v_val_397_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg___boxed(lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_a_400_, lean_object* v_l_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_Internal_List_getValue_x21___redArg(v_inst_398_, v_inst_399_, v_a_400_, v_l_401_);
lean_dec(v_inst_399_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_a_407_, lean_object* v_l_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Std_Internal_List_getValue_x21___redArg(v_inst_405_, v_inst_406_, v_a_407_, v_l_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___boxed(lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_a_414_, lean_object* v_l_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_Internal_List_getValue_x21(v_00_u03b1_410_, v_00_u03b2_411_, v_inst_412_, v_inst_413_, v_a_414_, v_l_415_);
lean_dec(v_inst_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f___redArg(lean_object* v_inst_417_, lean_object* v_a_418_, lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
lean_object* v___x_420_; 
lean_dec(v_a_418_);
lean_dec_ref(v_inst_417_);
v___x_420_ = lean_box(0);
return v___x_420_;
}
else
{
lean_object* v_head_421_; lean_object* v_tail_422_; lean_object* v_fst_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_head_421_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_head_421_);
v_tail_422_ = lean_ctor_get(v_x_419_, 1);
lean_inc(v_tail_422_);
lean_dec_ref_known(v_x_419_, 2);
v_fst_423_ = lean_ctor_get(v_head_421_, 0);
lean_inc_n(v_fst_423_, 2);
lean_dec(v_head_421_);
lean_inc_ref(v_inst_417_);
lean_inc(v_a_418_);
v___x_424_ = lean_apply_2(v_inst_417_, v_fst_423_, v_a_418_);
v___x_425_ = lean_unbox(v___x_424_);
if (v___x_425_ == 0)
{
lean_dec(v_fst_423_);
v_x_419_ = v_tail_422_;
goto _start;
}
else
{
lean_object* v___x_427_; 
lean_dec(v_tail_422_);
lean_dec(v_a_418_);
lean_dec_ref(v_inst_417_);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v_fst_423_);
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b2_429_, lean_object* v_inst_430_, lean_object* v_a_431_, lean_object* v_x_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_430_, v_a_431_, v_x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey___redArg(lean_object* v_inst_434_, lean_object* v_a_435_, lean_object* v_l_436_){
_start:
{
lean_object* v___x_437_; lean_object* v_val_438_; 
v___x_437_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_434_, v_a_435_, v_l_436_);
v_val_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_438_);
lean_dec(v___x_437_);
return v_val_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_inst_441_, lean_object* v_a_442_, lean_object* v_l_443_, lean_object* v_h_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_Internal_List_getKey___redArg(v_inst_441_, v_a_442_, v_l_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg(lean_object* v_inst_446_, lean_object* v_a_447_, lean_object* v_l_448_, lean_object* v_fallback_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_446_, v_a_447_, v_l_448_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_inc(v_fallback_449_);
return v_fallback_449_;
}
else
{
lean_object* v_val_451_; 
v_val_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v___x_450_, 1);
return v_val_451_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg___boxed(lean_object* v_inst_452_, lean_object* v_a_453_, lean_object* v_l_454_, lean_object* v_fallback_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_Internal_List_getKeyD___redArg(v_inst_452_, v_a_453_, v_l_454_, v_fallback_455_);
lean_dec(v_fallback_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD(lean_object* v_00_u03b1_457_, lean_object* v_00_u03b2_458_, lean_object* v_inst_459_, lean_object* v_a_460_, lean_object* v_l_461_, lean_object* v_fallback_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_Internal_List_getKeyD___redArg(v_inst_459_, v_a_460_, v_l_461_, v_fallback_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___boxed(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_inst_466_, lean_object* v_a_467_, lean_object* v_l_468_, lean_object* v_fallback_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Internal_List_getKeyD(v_00_u03b1_464_, v_00_u03b2_465_, v_inst_466_, v_a_467_, v_l_468_, v_fallback_469_);
lean_dec(v_fallback_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg(lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_a_473_, lean_object* v_l_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_471_, v_a_473_, v_l_474_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_477_ = l_panic___redArg(v_inst_472_, v___x_476_);
return v___x_477_;
}
else
{
lean_object* v_val_478_; 
v_val_478_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v___x_475_, 1);
return v_val_478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg___boxed(lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_a_481_, lean_object* v_l_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_Internal_List_getKey_x21___redArg(v_inst_479_, v_inst_480_, v_a_481_, v_l_482_);
lean_dec(v_inst_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_a_488_, lean_object* v_l_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_Internal_List_getKey_x21___redArg(v_inst_486_, v_inst_487_, v_a_488_, v_l_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___boxed(lean_object* v_00_u03b1_491_, lean_object* v_00_u03b2_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_a_495_, lean_object* v_l_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_Internal_List_getKey_x21(v_00_u03b1_491_, v_00_u03b2_492_, v_inst_493_, v_inst_494_, v_a_495_, v_l_496_);
lean_dec(v_inst_494_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry___redArg(lean_object* v_inst_498_, lean_object* v_k_499_, lean_object* v_v_500_, lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_501_) == 0)
{
lean_object* v___x_502_; 
lean_dec(v_v_500_);
lean_dec(v_k_499_);
lean_dec_ref(v_inst_498_);
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v_head_503_; lean_object* v_tail_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_527_; 
v_head_503_ = lean_ctor_get(v_x_501_, 0);
v_tail_504_ = lean_ctor_get(v_x_501_, 1);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_501_);
if (v_isSharedCheck_527_ == 0)
{
v___x_506_ = v_x_501_;
v_isShared_507_ = v_isSharedCheck_527_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_tail_504_);
lean_inc(v_head_503_);
lean_dec(v_x_501_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_527_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_fst_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_fst_508_ = lean_ctor_get(v_head_503_, 0);
lean_inc_ref(v_inst_498_);
lean_inc(v_k_499_);
lean_inc(v_fst_508_);
v___x_509_ = lean_apply_2(v_inst_498_, v_fst_508_, v_k_499_);
v___x_510_ = lean_unbox(v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_498_, v_k_499_, v_v_500_, v_tail_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v___x_511_);
v___x_513_ = v___x_506_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_head_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_inst_498_);
v_isSharedCheck_524_ = !lean_is_exclusive(v_head_503_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; lean_object* v_unused_526_; 
v_unused_525_ = lean_ctor_get(v_head_503_, 1);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v_head_503_, 0);
lean_dec(v_unused_526_);
v___x_516_ = v_head_503_;
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
else
{
lean_dec(v_head_503_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_v_500_);
lean_ctor_set(v___x_516_, 0, v_k_499_);
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_k_499_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_v_500_);
v___x_519_ = v_reuseFailAlloc_523_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_521_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_519_);
v___x_521_ = v___x_506_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_tail_504_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry(lean_object* v_00_u03b1_528_, lean_object* v_00_u03b2_529_, lean_object* v_inst_530_, lean_object* v_k_531_, lean_object* v_v_532_, lean_object* v_x_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_530_, v_k_531_, v_v_532_, v_x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey___redArg(lean_object* v_inst_535_, lean_object* v_k_536_, lean_object* v_x_537_){
_start:
{
if (lean_obj_tag(v_x_537_) == 0)
{
lean_object* v___x_538_; 
lean_dec(v_k_536_);
lean_dec_ref(v_inst_535_);
v___x_538_ = lean_box(0);
return v___x_538_;
}
else
{
lean_object* v_head_539_; lean_object* v_tail_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_551_; 
v_head_539_ = lean_ctor_get(v_x_537_, 0);
v_tail_540_ = lean_ctor_get(v_x_537_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_537_);
if (v_isSharedCheck_551_ == 0)
{
v___x_542_ = v_x_537_;
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_tail_540_);
lean_inc(v_head_539_);
lean_dec(v_x_537_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_fst_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_fst_544_ = lean_ctor_get(v_head_539_, 0);
lean_inc_ref(v_inst_535_);
lean_inc(v_k_536_);
lean_inc(v_fst_544_);
v___x_545_ = lean_apply_2(v_inst_535_, v_fst_544_, v_k_536_);
v___x_546_ = lean_unbox(v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = l_Std_Internal_List_eraseKey___redArg(v_inst_535_, v_k_536_, v_tail_540_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_547_);
v___x_549_ = v___x_542_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_head_539_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
else
{
lean_del_object(v___x_542_);
lean_dec(v_head_539_);
lean_dec(v_k_536_);
lean_dec_ref(v_inst_535_);
return v_tail_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey(lean_object* v_00_u03b1_552_, lean_object* v_00_u03b2_553_, lean_object* v_inst_554_, lean_object* v_k_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_Internal_List_eraseKey___redArg(v_inst_554_, v_k_555_, v_x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry___redArg(lean_object* v_inst_558_, lean_object* v_k_559_, lean_object* v_v_560_, lean_object* v_l_561_){
_start:
{
uint8_t v___x_562_; 
lean_inc(v_l_561_);
lean_inc(v_k_559_);
lean_inc_ref(v_inst_558_);
v___x_562_ = l_Std_Internal_List_containsKey___redArg(v_inst_558_, v_k_559_, v_l_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v_inst_558_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_k_559_);
lean_ctor_set(v___x_563_, 1, v_v_560_);
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_l_561_);
return v___x_564_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_558_, v_k_559_, v_v_560_, v_l_561_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry(lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_, lean_object* v_inst_568_, lean_object* v_k_569_, lean_object* v_v_570_, lean_object* v_l_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Std_Internal_List_insertEntry___redArg(v_inst_568_, v_k_569_, v_v_570_, v_l_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew___redArg(lean_object* v_inst_573_, lean_object* v_k_574_, lean_object* v_v_575_, lean_object* v_l_576_){
_start:
{
uint8_t v___x_577_; 
lean_inc(v_l_576_);
lean_inc(v_k_574_);
v___x_577_ = l_Std_Internal_List_containsKey___redArg(v_inst_573_, v_k_574_, v_l_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_k_574_);
lean_ctor_set(v___x_578_, 1, v_v_575_);
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_l_576_);
return v___x_579_;
}
else
{
lean_dec(v_v_575_);
lean_dec(v_k_574_);
return v_l_576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew(lean_object* v_00_u03b1_580_, lean_object* v_00_u03b2_581_, lean_object* v_inst_582_, lean_object* v_k_583_, lean_object* v_v_584_, lean_object* v_l_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_582_, v_k_583_, v_v_584_, v_l_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_587_, lean_object* v_h__1_588_, lean_object* v_h__2_589_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v_h__2_589_);
v___x_590_ = lean_box(0);
v___x_591_ = lean_apply_1(v_h__1_588_, v___x_590_);
return v___x_591_;
}
else
{
lean_object* v_val_592_; lean_object* v___x_593_; 
lean_dec(v_h__1_588_);
v_val_592_ = lean_ctor_get(v_x_587_, 0);
lean_inc(v_val_592_);
lean_dec_ref_known(v_x_587_, 1);
v___x_593_ = lean_apply_1(v_h__2_589_, v_val_592_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_594_, lean_object* v_motive_595_, lean_object* v_x_596_, lean_object* v_h__1_597_, lean_object* v_h__2_598_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v_h__2_598_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_apply_1(v_h__1_597_, v___x_599_);
return v___x_600_;
}
else
{
lean_object* v_val_601_; lean_object* v___x_602_; 
lean_dec(v_h__1_597_);
v_val_601_ = lean_ctor_get(v_x_596_, 0);
lean_inc(v_val_601_);
lean_dec_ref_known(v_x_596_, 1);
v___x_602_ = lean_apply_1(v_h__2_598_, v_val_601_);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_603_, lean_object* v_h__1_604_, lean_object* v_h__2_605_){
_start:
{
if (lean_obj_tag(v_x_603_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_607_; 
lean_dec(v_h__2_605_);
v_a_606_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v_x_603_, 1);
v___x_607_ = lean_apply_1(v_h__1_604_, v_a_606_);
return v___x_607_;
}
else
{
lean_object* v_a_608_; lean_object* v___x_609_; 
lean_dec(v_h__1_604_);
v_a_608_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v_x_603_, 1);
v___x_609_ = lean_apply_1(v_h__2_605_, v_a_608_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_610_, lean_object* v_motive_611_, lean_object* v_x_612_, lean_object* v_h__1_613_, lean_object* v_h__2_614_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_616_; 
lean_dec(v_h__2_614_);
v_a_615_ = lean_ctor_get(v_x_612_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v_x_612_, 1);
v___x_616_ = lean_apply_1(v_h__1_613_, v_a_615_);
return v___x_616_;
}
else
{
lean_object* v_a_617_; lean_object* v___x_618_; 
lean_dec(v_h__1_613_);
v_a_617_ = lean_ctor_get(v_x_612_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v_x_612_, 1);
v___x_618_ = lean_apply_1(v_h__2_614_, v_a_617_);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList___redArg(lean_object* v_inst_619_, lean_object* v_l_620_, lean_object* v_toInsert_621_){
_start:
{
if (lean_obj_tag(v_toInsert_621_) == 0)
{
lean_dec_ref(v_inst_619_);
return v_l_620_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v_fst_624_; lean_object* v_snd_625_; lean_object* v___x_626_; 
v_head_622_ = lean_ctor_get(v_toInsert_621_, 0);
lean_inc(v_head_622_);
v_tail_623_ = lean_ctor_get(v_toInsert_621_, 1);
lean_inc(v_tail_623_);
lean_dec_ref_known(v_toInsert_621_, 2);
v_fst_624_ = lean_ctor_get(v_head_622_, 0);
lean_inc(v_fst_624_);
v_snd_625_ = lean_ctor_get(v_head_622_, 1);
lean_inc(v_snd_625_);
lean_dec(v_head_622_);
lean_inc_ref(v_inst_619_);
v___x_626_ = l_Std_Internal_List_insertEntry___redArg(v_inst_619_, v_fst_624_, v_snd_625_, v_l_620_);
v_l_620_ = v___x_626_;
v_toInsert_621_ = v_tail_623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_inst_630_, lean_object* v_l_631_, lean_object* v_toInsert_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_Internal_List_insertList___redArg(v_inst_630_, v_l_631_, v_toInsert_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_634_, lean_object* v_h__1_635_, lean_object* v_h__2_636_){
_start:
{
if (lean_obj_tag(v_x_634_) == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v_h__2_636_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_apply_1(v_h__1_635_, v___x_637_);
return v___x_638_;
}
else
{
lean_object* v_head_639_; lean_object* v_tail_640_; lean_object* v_fst_641_; lean_object* v_snd_642_; lean_object* v___x_643_; 
lean_dec(v_h__1_635_);
v_head_639_ = lean_ctor_get(v_x_634_, 0);
lean_inc(v_head_639_);
v_tail_640_ = lean_ctor_get(v_x_634_, 1);
lean_inc(v_tail_640_);
lean_dec_ref_known(v_x_634_, 2);
v_fst_641_ = lean_ctor_get(v_head_639_, 0);
lean_inc(v_fst_641_);
v_snd_642_ = lean_ctor_get(v_head_639_, 1);
lean_inc(v_snd_642_);
lean_dec(v_head_639_);
v___x_643_ = lean_apply_3(v_h__2_636_, v_fst_641_, v_snd_642_, v_tail_640_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_644_, lean_object* v_00_u03b2_645_, lean_object* v_motive_646_, lean_object* v_x_647_, lean_object* v_h__1_648_, lean_object* v_h__2_649_){
_start:
{
if (lean_obj_tag(v_x_647_) == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec(v_h__2_649_);
v___x_650_ = lean_box(0);
v___x_651_ = lean_apply_1(v_h__1_648_, v___x_650_);
return v___x_651_;
}
else
{
lean_object* v_head_652_; lean_object* v_tail_653_; lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_656_; 
lean_dec(v_h__1_648_);
v_head_652_ = lean_ctor_get(v_x_647_, 0);
lean_inc(v_head_652_);
v_tail_653_ = lean_ctor_get(v_x_647_, 1);
lean_inc(v_tail_653_);
lean_dec_ref_known(v_x_647_, 2);
v_fst_654_ = lean_ctor_get(v_head_652_, 0);
lean_inc(v_fst_654_);
v_snd_655_ = lean_ctor_get(v_head_652_, 1);
lean_inc(v_snd_655_);
lean_dec(v_head_652_);
v___x_656_ = lean_apply_3(v_h__2_649_, v_fst_654_, v_snd_655_, v_tail_653_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew___redArg(lean_object* v_inst_657_, lean_object* v_l_658_, lean_object* v_toInsert_659_){
_start:
{
if (lean_obj_tag(v_toInsert_659_) == 0)
{
lean_dec_ref(v_inst_657_);
return v_l_658_;
}
else
{
lean_object* v_head_660_; lean_object* v_tail_661_; lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_664_; 
v_head_660_ = lean_ctor_get(v_toInsert_659_, 0);
lean_inc(v_head_660_);
v_tail_661_ = lean_ctor_get(v_toInsert_659_, 1);
lean_inc(v_tail_661_);
lean_dec_ref_known(v_toInsert_659_, 2);
v_fst_662_ = lean_ctor_get(v_head_660_, 0);
lean_inc(v_fst_662_);
v_snd_663_ = lean_ctor_get(v_head_660_, 1);
lean_inc(v_snd_663_);
lean_dec(v_head_660_);
lean_inc_ref(v_inst_657_);
v___x_664_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_657_, v_fst_662_, v_snd_663_, v_l_658_);
v_l_658_ = v___x_664_;
v_toInsert_659_ = v_tail_661_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b2_667_, lean_object* v_inst_668_, lean_object* v_l_669_, lean_object* v_toInsert_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_Internal_List_insertListIfNew___redArg(v_inst_668_, v_l_669_, v_toInsert_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList___redArg(lean_object* v_inst_672_, lean_object* v_l_u2081_673_, lean_object* v_l_u2082_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_675_ = l_List_lengthTR___redArg(v_l_u2081_673_);
v___x_676_ = l_List_lengthTR___redArg(v_l_u2082_674_);
v___x_677_ = lean_nat_dec_le(v___x_675_, v___x_676_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_Internal_List_insertList___redArg(v_inst_672_, v_l_u2081_673_, v_l_u2082_674_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_Internal_List_insertListIfNew___redArg(v_inst_672_, v_l_u2082_674_, v_l_u2081_673_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_inst_682_, lean_object* v_l_u2081_683_, lean_object* v_l_u2082_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_Internal_List_insertSmallerList___redArg(v_inst_682_, v_l_u2081_683_, v_l_u2082_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma___redArg(lean_object* v_p_686_){
_start:
{
lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_fst_687_ = lean_ctor_get(v_p_686_, 0);
v_snd_688_ = lean_ctor_get(v_p_686_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_p_686_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v_p_686_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_snd_688_);
lean_inc(v_fst_687_);
lean_dec(v_p_686_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_fst_687_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_snd_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma(lean_object* v_00_u03b1_696_, lean_object* v_00_u03b2_697_, lean_object* v_p_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_Internal_List_Prod_toSigma___redArg(v_p_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst___redArg(lean_object* v_inst_701_, lean_object* v_l_702_, lean_object* v_toInsert_703_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = ((lean_object*)(l_Std_Internal_List_insertListConst___redArg___closed__0));
v___x_705_ = lean_box(0);
v___x_706_ = l_List_mapTR_loop___redArg(v___x_704_, v_toInsert_703_, v___x_705_);
v___x_707_ = l_Std_Internal_List_insertList___redArg(v_inst_701_, v_l_702_, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_inst_710_, lean_object* v_l_711_, lean_object* v_toInsert_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_Internal_List_insertListConst___redArg(v_inst_710_, v_l_711_, v_toInsert_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit___redArg(lean_object* v_inst_714_, lean_object* v_l_715_, lean_object* v_toInsert_716_){
_start:
{
if (lean_obj_tag(v_toInsert_716_) == 0)
{
lean_dec_ref(v_inst_714_);
return v_l_715_;
}
else
{
lean_object* v_head_717_; lean_object* v_tail_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_head_717_ = lean_ctor_get(v_toInsert_716_, 0);
lean_inc(v_head_717_);
v_tail_718_ = lean_ctor_get(v_toInsert_716_, 1);
lean_inc(v_tail_718_);
lean_dec_ref_known(v_toInsert_716_, 2);
v___x_719_ = lean_box(0);
lean_inc_ref(v_inst_714_);
v___x_720_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_714_, v_head_717_, v___x_719_, v_l_715_);
v_l_715_ = v___x_720_;
v_toInsert_716_ = v_tail_718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit(lean_object* v_00_u03b1_722_, lean_object* v_inst_723_, lean_object* v_l_724_, lean_object* v_toInsert_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Std_Internal_List_insertListIfNewUnit___redArg(v_inst_723_, v_l_724_, v_toInsert_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(lean_object* v_toInsert_727_, lean_object* v_h__1_728_, lean_object* v_h__2_729_){
_start:
{
if (lean_obj_tag(v_toInsert_727_) == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec(v_h__2_729_);
v___x_730_ = lean_box(0);
v___x_731_ = lean_apply_1(v_h__1_728_, v___x_730_);
return v___x_731_;
}
else
{
lean_object* v_head_732_; lean_object* v_tail_733_; lean_object* v___x_734_; 
lean_dec(v_h__1_728_);
v_head_732_ = lean_ctor_get(v_toInsert_727_, 0);
lean_inc(v_head_732_);
v_tail_733_ = lean_ctor_get(v_toInsert_727_, 1);
lean_inc(v_tail_733_);
lean_dec_ref_known(v_toInsert_727_, 2);
v___x_734_ = lean_apply_2(v_h__2_729_, v_head_732_, v_tail_733_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object* v_00_u03b1_735_, lean_object* v_motive_736_, lean_object* v_toInsert_737_, lean_object* v_h__1_738_, lean_object* v_h__2_739_){
_start:
{
if (lean_obj_tag(v_toInsert_737_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_h__2_739_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_apply_1(v_h__1_738_, v___x_740_);
return v___x_741_;
}
else
{
lean_object* v_head_742_; lean_object* v_tail_743_; lean_object* v___x_744_; 
lean_dec(v_h__1_738_);
v_head_742_ = lean_ctor_get(v_toInsert_737_, 0);
lean_inc(v_head_742_);
v_tail_743_ = lean_ctor_get(v_toInsert_737_, 1);
lean_inc(v_tail_743_);
lean_dec_ref_known(v_toInsert_737_, 2);
v___x_744_ = lean_apply_2(v_h__2_739_, v_head_742_, v_tail_743_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey___redArg(lean_object* v_inst_745_, lean_object* v_k_746_, lean_object* v_f_747_, lean_object* v_l_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_inc(v_l_748_);
lean_inc(v_k_746_);
lean_inc_ref(v_inst_745_);
v___x_749_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_745_, v_k_746_, v_l_748_);
v___x_750_ = lean_apply_1(v_f_747_, v___x_749_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_Internal_List_eraseKey___redArg(v_inst_745_, v_k_746_, v_l_748_);
return v___x_751_;
}
else
{
lean_object* v_val_752_; lean_object* v___x_753_; 
v_val_752_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v___x_750_, 1);
v___x_753_ = l_Std_Internal_List_insertEntry___redArg(v_inst_745_, v_k_746_, v_val_752_, v_l_748_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey(lean_object* v_00_u03b1_754_, lean_object* v_00_u03b2_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_k_758_, lean_object* v_f_759_, lean_object* v_l_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_Internal_List_alterKey___redArg(v_inst_756_, v_k_758_, v_f_759_, v_l_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object* v_x_762_, lean_object* v_h__1_763_, lean_object* v_h__2_764_){
_start:
{
if (lean_obj_tag(v_x_762_) == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec(v_h__2_764_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_apply_1(v_h__1_763_, v___x_765_);
return v___x_766_;
}
else
{
lean_object* v_val_767_; lean_object* v___x_768_; 
lean_dec(v_h__1_763_);
v_val_767_ = lean_ctor_get(v_x_762_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v_x_762_, 1);
v___x_768_ = lean_apply_1(v_h__2_764_, v_val_767_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* v_00_u03b1_769_, lean_object* v_00_u03b2_770_, lean_object* v_k_771_, lean_object* v_motive_772_, lean_object* v_x_773_, lean_object* v_h__1_774_, lean_object* v_h__2_775_){
_start:
{
if (lean_obj_tag(v_x_773_) == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec(v_h__2_775_);
v___x_776_ = lean_box(0);
v___x_777_ = lean_apply_1(v_h__1_774_, v___x_776_);
return v___x_777_;
}
else
{
lean_object* v_val_778_; lean_object* v___x_779_; 
lean_dec(v_h__1_774_);
v_val_778_ = lean_ctor_get(v_x_773_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v_x_773_, 1);
v___x_779_ = lean_apply_1(v_h__2_775_, v_val_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_k_782_, lean_object* v_motive_783_, lean_object* v_x_784_, lean_object* v_h__1_785_, lean_object* v_h__2_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_780_, v_00_u03b2_781_, v_k_782_, v_motive_783_, v_x_784_, v_h__1_785_, v_h__2_786_);
lean_dec(v_k_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_788_, lean_object* v_h__1_789_, lean_object* v_h__2_790_){
_start:
{
if (lean_obj_tag(v_x_788_) == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec(v_h__2_790_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_apply_1(v_h__1_789_, v___x_791_);
return v___x_792_;
}
else
{
lean_object* v_val_793_; lean_object* v___x_794_; 
lean_dec(v_h__1_789_);
v_val_793_ = lean_ctor_get(v_x_788_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v_x_788_, 1);
v___x_794_ = lean_apply_1(v_h__2_790_, v_val_793_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_k_797_, lean_object* v_motive_798_, lean_object* v_x_799_, lean_object* v_h__1_800_, lean_object* v_h__2_801_){
_start:
{
if (lean_obj_tag(v_x_799_) == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec(v_h__2_801_);
v___x_802_ = lean_box(0);
v___x_803_ = lean_apply_1(v_h__1_800_, v___x_802_);
return v___x_803_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_805_; 
lean_dec(v_h__1_800_);
v_val_804_ = lean_ctor_get(v_x_799_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v_x_799_, 1);
v___x_805_ = lean_apply_1(v_h__2_801_, v_val_804_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_806_, lean_object* v_00_u03b2_807_, lean_object* v_k_808_, lean_object* v_motive_809_, lean_object* v_x_810_, lean_object* v_h__1_811_, lean_object* v_h__2_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_806_, v_00_u03b2_807_, v_k_808_, v_motive_809_, v_x_810_, v_h__1_811_, v_h__2_812_);
lean_dec(v_k_808_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey___redArg(lean_object* v_inst_814_, lean_object* v_k_815_, lean_object* v_f_816_, lean_object* v_l_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_inc(v_l_817_);
lean_inc(v_k_815_);
lean_inc_ref(v_inst_814_);
v___x_818_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_814_, v_k_815_, v_l_817_);
v___x_819_ = lean_apply_1(v_f_816_, v___x_818_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_Internal_List_eraseKey___redArg(v_inst_814_, v_k_815_, v_l_817_);
return v___x_820_;
}
else
{
lean_object* v_val_821_; lean_object* v___x_822_; 
v_val_821_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v___x_819_, 1);
v___x_822_ = l_Std_Internal_List_insertEntry___redArg(v_inst_814_, v_k_815_, v_val_821_, v_l_817_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_inst_825_, lean_object* v_k_826_, lean_object* v_f_827_, lean_object* v_l_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_Internal_List_Const_alterKey___redArg(v_inst_825_, v_k_826_, v_f_827_, v_l_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object* v_x_830_, lean_object* v_h__1_831_, lean_object* v_h__2_832_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec(v_h__2_832_);
v___x_833_ = lean_box(0);
v___x_834_ = lean_apply_1(v_h__1_831_, v___x_833_);
return v___x_834_;
}
else
{
lean_object* v_val_835_; lean_object* v___x_836_; 
lean_dec(v_h__1_831_);
v_val_835_ = lean_ctor_get(v_x_830_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v_x_830_, 1);
v___x_836_ = lean_apply_1(v_h__2_832_, v_val_835_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* v_00_u03b2_837_, lean_object* v_motive_838_, lean_object* v_x_839_, lean_object* v_h__1_840_, lean_object* v_h__2_841_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec(v_h__2_841_);
v___x_842_ = lean_box(0);
v___x_843_ = lean_apply_1(v_h__1_840_, v___x_842_);
return v___x_843_;
}
else
{
lean_object* v_val_844_; lean_object* v___x_845_; 
lean_dec(v_h__1_840_);
v_val_844_ = lean_ctor_get(v_x_839_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v_x_839_, 1);
v___x_845_ = lean_apply_1(v_h__2_841_, v_val_844_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_846_, lean_object* v_h__1_847_, lean_object* v_h__2_848_){
_start:
{
if (lean_obj_tag(v_x_846_) == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v_h__2_848_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_apply_1(v_h__1_847_, v___x_849_);
return v___x_850_;
}
else
{
lean_object* v_val_851_; lean_object* v___x_852_; 
lean_dec(v_h__1_847_);
v_val_851_ = lean_ctor_get(v_x_846_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v_x_846_, 1);
v___x_852_ = lean_apply_1(v_h__2_848_, v_val_851_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b2_853_, lean_object* v_motive_854_, lean_object* v_x_855_, lean_object* v_h__1_856_, lean_object* v_h__2_857_){
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
lean_dec_ref_known(v_x_855_, 1);
v___x_861_ = lean_apply_1(v_h__2_857_, v_val_860_);
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey___redArg(lean_object* v_inst_862_, lean_object* v_k_863_, lean_object* v_f_864_, lean_object* v_l_865_){
_start:
{
lean_object* v___x_866_; 
lean_inc(v_l_865_);
lean_inc(v_k_863_);
lean_inc_ref(v_inst_862_);
v___x_866_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_862_, v_k_863_, v_l_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_dec(v_f_864_);
lean_dec(v_k_863_);
lean_dec_ref(v_inst_862_);
return v_l_865_;
}
else
{
lean_object* v_val_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_val_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_val_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = lean_apply_1(v_f_864_, v_val_867_);
v___x_869_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_862_, v_k_863_, v___x_868_, v_l_865_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_inst_872_, lean_object* v_inst_873_, lean_object* v_k_874_, lean_object* v_f_875_, lean_object* v_l_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Std_Internal_List_modifyKey___redArg(v_inst_872_, v_k_874_, v_f_875_, v_l_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey___redArg(lean_object* v_inst_878_, lean_object* v_k_879_, lean_object* v_f_880_, lean_object* v_l_881_){
_start:
{
lean_object* v___x_882_; 
lean_inc(v_l_881_);
lean_inc(v_k_879_);
lean_inc_ref(v_inst_878_);
v___x_882_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_878_, v_k_879_, v_l_881_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_dec(v_f_880_);
lean_dec(v_k_879_);
lean_dec_ref(v_inst_878_);
return v_l_881_;
}
else
{
lean_object* v_val_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_val_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = lean_apply_1(v_f_880_, v_val_883_);
v___x_885_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_878_, v_k_879_, v___x_884_, v_l_881_);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey(lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_inst_888_, lean_object* v_k_889_, lean_object* v_f_890_, lean_object* v_l_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_Internal_List_Const_modifyKey___redArg(v_inst_888_, v_k_889_, v_f_890_, v_l_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_893_, lean_object* v_h__1_894_, lean_object* v_h__2_895_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec(v_h__1_894_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_apply_1(v_h__2_895_, v___x_896_);
return v___x_897_;
}
else
{
lean_object* v_val_898_; lean_object* v___x_899_; 
lean_dec(v_h__2_895_);
v_val_898_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_val_898_);
lean_dec_ref_known(v_x_893_, 1);
v___x_899_ = lean_apply_1(v_h__1_894_, v_val_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_900_, lean_object* v_motive_901_, lean_object* v_x_902_, lean_object* v_h__1_903_, lean_object* v_h__2_904_){
_start:
{
if (lean_obj_tag(v_x_902_) == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec(v_h__1_903_);
v___x_905_ = lean_box(0);
v___x_906_ = lean_apply_1(v_h__2_904_, v___x_905_);
return v___x_906_;
}
else
{
lean_object* v_val_907_; lean_object* v___x_908_; 
lean_dec(v_h__2_904_);
v_val_907_ = lean_ctor_get(v_x_902_, 0);
lean_inc(v_val_907_);
lean_dec_ref_known(v_x_902_, 1);
v___x_908_ = lean_apply_1(v_h__1_903_, v_val_907_);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___redArg(lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_h__1_911_, lean_object* v_h__2_912_){
_start:
{
if (lean_obj_tag(v_x_909_) == 0)
{
lean_object* v___x_913_; 
lean_dec(v_h__2_912_);
v___x_913_ = lean_apply_1(v_h__1_911_, v_x_910_);
return v___x_913_;
}
else
{
lean_object* v_val_914_; lean_object* v___x_915_; 
lean_dec(v_h__1_911_);
v_val_914_ = lean_ctor_get(v_x_909_, 0);
lean_inc(v_val_914_);
lean_dec_ref_known(v_x_909_, 1);
v___x_915_ = lean_apply_2(v_h__2_912_, v_val_914_, v_x_910_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(lean_object* v_00_u03b1_916_, lean_object* v_00_u03b2_917_, lean_object* v_motive_918_, lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_h__1_921_, lean_object* v_h__2_922_){
_start:
{
if (lean_obj_tag(v_x_919_) == 0)
{
lean_object* v___x_923_; 
lean_dec(v_h__2_922_);
v___x_923_ = lean_apply_1(v_h__1_921_, v_x_920_);
return v___x_923_;
}
else
{
lean_object* v_val_924_; lean_object* v___x_925_; 
lean_dec(v_h__1_921_);
v_val_924_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_val_924_);
lean_dec_ref_known(v_x_919_, 1);
v___x_925_ = lean_apply_2(v_h__2_922_, v_val_924_, v_x_920_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList___redArg(lean_object* v_inst_926_, lean_object* v_l_927_, lean_object* v_toErase_928_){
_start:
{
if (lean_obj_tag(v_toErase_928_) == 0)
{
lean_dec_ref(v_inst_926_);
return v_l_927_;
}
else
{
lean_object* v_head_929_; lean_object* v_tail_930_; lean_object* v___x_931_; 
v_head_929_ = lean_ctor_get(v_toErase_928_, 0);
lean_inc(v_head_929_);
v_tail_930_ = lean_ctor_get(v_toErase_928_, 1);
lean_inc(v_tail_930_);
lean_dec_ref_known(v_toErase_928_, 2);
lean_inc_ref(v_inst_926_);
v___x_931_ = l_Std_Internal_List_eraseKey___redArg(v_inst_926_, v_head_929_, v_l_927_);
v_l_927_ = v___x_931_;
v_toErase_928_ = v_tail_930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList(lean_object* v_00_u03b1_933_, lean_object* v_00_u03b2_934_, lean_object* v_inst_935_, lean_object* v_l_936_, lean_object* v_toErase_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Std_Internal_List_eraseList___redArg(v_inst_935_, v_l_936_, v_toErase_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_939_, lean_object* v_h__1_940_, lean_object* v_h__2_941_){
_start:
{
if (lean_obj_tag(v_opt_939_) == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_h__1_940_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_apply_1(v_h__2_941_, v___x_942_);
return v___x_943_;
}
else
{
lean_object* v_val_944_; lean_object* v___x_945_; 
lean_dec(v_h__2_941_);
v_val_944_ = lean_ctor_get(v_opt_939_, 0);
lean_inc(v_val_944_);
lean_dec_ref_known(v_opt_939_, 1);
v___x_945_ = lean_apply_1(v_h__1_940_, v_val_944_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_946_, lean_object* v_motive_947_, lean_object* v_opt_948_, lean_object* v_h__1_949_, lean_object* v_h__2_950_){
_start:
{
if (lean_obj_tag(v_opt_948_) == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_h__1_949_);
v___x_951_ = lean_box(0);
v___x_952_ = lean_apply_1(v_h__2_950_, v___x_951_);
return v___x_952_;
}
else
{
lean_object* v_val_953_; lean_object* v___x_954_; 
lean_dec(v_h__2_950_);
v_val_953_ = lean_ctor_get(v_opt_948_, 0);
lean_inc(v_val_953_);
lean_dec_ref_known(v_opt_948_, 1);
v___x_954_ = lean_apply_1(v_h__1_949_, v_val_953_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___redArg(){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = lean_box(0);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___redArg___boxed(lean_object* v___dummy_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___redArg();
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(lean_object* v_00_u03b1_959_, lean_object* v_00_u03b2_960_, lean_object* v_inst_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_box(0);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___boxed(lean_object* v_00_u03b1_963_, lean_object* v_00_u03b2_964_, lean_object* v_inst_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(v_00_u03b1_963_, v_00_u03b2_964_, v_inst_965_);
lean_dec_ref(v_inst_965_);
return v_res_966_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(lean_object* v_inst_967_, lean_object* v_a_968_, lean_object* v_b_969_){
_start:
{
lean_object* v_fst_970_; lean_object* v_fst_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v_fst_970_ = lean_ctor_get(v_a_968_, 0);
lean_inc(v_fst_970_);
lean_dec_ref(v_a_968_);
v_fst_971_ = lean_ctor_get(v_b_969_, 0);
lean_inc(v_fst_971_);
lean_dec_ref(v_b_969_);
v___x_972_ = lean_apply_2(v_inst_967_, v_fst_970_, v_fst_971_);
v___x_973_ = lean_unbox(v___x_972_);
if (v___x_973_ == 2)
{
uint8_t v___x_974_; 
v___x_974_ = 0;
return v___x_974_;
}
else
{
uint8_t v___x_975_; 
v___x_975_ = 1;
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg___boxed(lean_object* v_inst_976_, lean_object* v_a_977_, lean_object* v_b_978_){
_start:
{
uint8_t v_res_979_; lean_object* v_r_980_; 
v_res_979_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_976_, v_a_977_, v_b_978_);
v_r_980_ = lean_box(v_res_979_);
return v_r_980_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(lean_object* v_00_u03b1_981_, lean_object* v_00_u03b2_982_, lean_object* v_inst_983_, lean_object* v_a_984_, lean_object* v_b_985_){
_start:
{
uint8_t v___x_986_; 
v___x_986_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_983_, v_a_984_, v_b_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___boxed(lean_object* v_00_u03b1_987_, lean_object* v_00_u03b2_988_, lean_object* v_inst_989_, lean_object* v_a_990_, lean_object* v_b_991_){
_start:
{
uint8_t v_res_992_; lean_object* v_r_993_; 
v_res_992_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(v_00_u03b1_987_, v_00_u03b2_988_, v_inst_989_, v_a_990_, v_b_991_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0(lean_object* v_inst_994_, lean_object* v_a_995_, lean_object* v_b_996_){
_start:
{
lean_object* v_fst_997_; lean_object* v_fst_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v_fst_997_ = lean_ctor_get(v_a_995_, 0);
v_fst_998_ = lean_ctor_get(v_b_996_, 0);
lean_inc(v_fst_998_);
lean_inc(v_fst_997_);
v___x_999_ = lean_apply_2(v_inst_994_, v_fst_997_, v_fst_998_);
v___x_1000_ = lean_unbox(v___x_999_);
if (v___x_1000_ == 2)
{
lean_dec_ref(v_a_995_);
return v_b_996_;
}
else
{
lean_dec_ref(v_b_996_);
return v_a_995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg(lean_object* v_inst_1001_){
_start:
{
lean_object* v___f_1002_; 
v___f_1002_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1002_, 0, v_inst_1001_);
return v___f_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd(lean_object* v_00_u03b1_1003_, lean_object* v_00_u03b2_1004_, lean_object* v_inst_1005_){
_start:
{
lean_object* v___f_1006_; 
v___f_1006_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1006_, 0, v_inst_1005_);
return v___f_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___redArg(lean_object* v_inst_1007_, lean_object* v_xs_1008_){
_start:
{
lean_object* v___f_1009_; lean_object* v___x_1010_; 
v___f_1009_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1009_, 0, v_inst_1007_);
v___x_1010_ = l_List_min_x3f___redArg(v___f_1009_, v_xs_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f(lean_object* v_00_u03b1_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_inst_1013_, lean_object* v_xs_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_1013_, v_xs_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___redArg(lean_object* v_inst_1016_, lean_object* v_xs_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_1016_, v_xs_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_box(0);
return v___x_1019_;
}
else
{
lean_object* v_val_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1028_; 
v_val_1020_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1022_ = v___x_1018_;
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_val_1020_);
lean_dec(v___x_1018_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_fst_1024_; lean_object* v___x_1026_; 
v_fst_1024_ = lean_ctor_get(v_val_1020_, 0);
lean_inc(v_fst_1024_);
lean_dec(v_val_1020_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v_fst_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_fst_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f(lean_object* v_00_u03b1_1029_, lean_object* v_00_u03b2_1030_, lean_object* v_inst_1031_, lean_object* v_xs_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1031_, v_xs_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___redArg(lean_object* v_x_1034_, lean_object* v_h__1_1035_, lean_object* v_h__2_1036_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec(v_h__2_1036_);
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_apply_1(v_h__1_1035_, v___x_1037_);
return v___x_1038_;
}
else
{
lean_object* v_val_1039_; lean_object* v___x_1040_; 
lean_dec(v_h__1_1035_);
v_val_1039_ = lean_ctor_get(v_x_1034_, 0);
lean_inc(v_val_1039_);
lean_dec_ref_known(v_x_1034_, 1);
v___x_1040_ = lean_apply_1(v_h__2_1036_, v_val_1039_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter(lean_object* v_00_u03b1_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_motive_1043_, lean_object* v_x_1044_, lean_object* v_h__1_1045_, lean_object* v_h__2_1046_){
_start:
{
if (lean_obj_tag(v_x_1044_) == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v_h__2_1046_);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_apply_1(v_h__1_1045_, v___x_1047_);
return v___x_1048_;
}
else
{
lean_object* v_val_1049_; lean_object* v___x_1050_; 
lean_dec(v_h__1_1045_);
v_val_1049_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_val_1049_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1050_ = lean_apply_1(v_h__2_1046_, v_val_1049_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_1051_, lean_object* v_h__1_1052_, lean_object* v_h__2_1053_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v_h__2_1053_);
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_apply_1(v_h__1_1052_, v___x_1054_);
return v___x_1055_;
}
else
{
lean_object* v_head_1056_; lean_object* v_tail_1057_; lean_object* v___x_1058_; 
lean_dec(v_h__1_1052_);
v_head_1056_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_head_1056_);
v_tail_1057_ = lean_ctor_get(v_x_1051_, 1);
lean_inc(v_tail_1057_);
lean_dec_ref_known(v_x_1051_, 2);
v___x_1058_ = lean_apply_2(v_h__2_1053_, v_head_1056_, v_tail_1057_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_1059_, lean_object* v_motive_1060_, lean_object* v_x_1061_, lean_object* v_h__1_1062_, lean_object* v_h__2_1063_){
_start:
{
if (lean_obj_tag(v_x_1061_) == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec(v_h__2_1063_);
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_apply_1(v_h__1_1062_, v___x_1064_);
return v___x_1065_;
}
else
{
lean_object* v_head_1066_; lean_object* v_tail_1067_; lean_object* v___x_1068_; 
lean_dec(v_h__1_1062_);
v_head_1066_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_head_1066_);
v_tail_1067_ = lean_ctor_get(v_x_1061_, 1);
lean_inc(v_tail_1067_);
lean_dec_ref_known(v_x_1061_, 2);
v___x_1068_ = lean_apply_2(v_h__2_1063_, v_head_1066_, v_tail_1067_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter___redArg(lean_object* v_x_1069_, lean_object* v_h__1_1070_, lean_object* v_h__2_1071_){
_start:
{
if (lean_obj_tag(v_x_1069_) == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec(v_h__2_1071_);
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_apply_1(v_h__1_1070_, v___x_1072_);
return v___x_1073_;
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1075_; 
lean_dec(v_h__1_1070_);
v_val_1074_ = lean_ctor_get(v_x_1069_, 0);
lean_inc(v_val_1074_);
lean_dec_ref_known(v_x_1069_, 1);
v___x_1075_ = lean_apply_1(v_h__2_1071_, v_val_1074_);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter(lean_object* v_00_u03b1_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_motive_1078_, lean_object* v_x_1079_, lean_object* v_h__1_1080_, lean_object* v_h__2_1081_){
_start:
{
if (lean_obj_tag(v_x_1079_) == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_h__2_1081_);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_apply_1(v_h__1_1080_, v___x_1082_);
return v___x_1083_;
}
else
{
lean_object* v_val_1084_; lean_object* v___x_1085_; 
lean_dec(v_h__1_1080_);
v_val_1084_ = lean_ctor_get(v_x_1079_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v_x_1079_, 1);
v___x_1085_ = lean_apply_1(v_h__2_1081_, v_val_1084_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___redArg(lean_object* v_inst_1086_, lean_object* v_xs_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v_val_1089_; 
v___x_1088_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1086_, v_xs_1087_);
v_val_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_val_1089_);
lean_dec(v___x_1088_);
return v_val_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey(lean_object* v_00_u03b1_1090_, lean_object* v_00_u03b2_1091_, lean_object* v_inst_1092_, lean_object* v_xs_1093_, lean_object* v_h_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Std_Internal_List_minKey___redArg(v_inst_1092_, v_xs_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___redArg(lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_xs_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1096_, v_xs_1098_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_1101_ = l_panic___redArg(v_inst_1097_, v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v_val_1102_; 
v_val_1102_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_val_1102_);
lean_dec_ref_known(v___x_1099_, 1);
return v_val_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___redArg___boxed(lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_xs_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_1103_, v_inst_1104_, v_xs_1105_);
lean_dec(v_inst_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21(lean_object* v_00_u03b1_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_xs_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_1109_, v_inst_1110_, v_xs_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___boxed(lean_object* v_00_u03b1_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_xs_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Std_Internal_List_minKey_x21(v_00_u03b1_1113_, v_00_u03b2_1114_, v_inst_1115_, v_inst_1116_, v_xs_1117_);
lean_dec(v_inst_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg(lean_object* v_inst_1119_, lean_object* v_xs_1120_, lean_object* v_fallback_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1119_, v_xs_1120_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_inc(v_fallback_1121_);
return v_fallback_1121_;
}
else
{
lean_object* v_val_1123_; 
v_val_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_val_1123_);
lean_dec_ref_known(v___x_1122_, 1);
return v_val_1123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg___boxed(lean_object* v_inst_1124_, lean_object* v_xs_1125_, lean_object* v_fallback_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_Internal_List_minKeyD___redArg(v_inst_1124_, v_xs_1125_, v_fallback_1126_);
lean_dec(v_fallback_1126_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD(lean_object* v_00_u03b1_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_inst_1130_, lean_object* v_xs_1131_, lean_object* v_fallback_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Std_Internal_List_minKeyD___redArg(v_inst_1130_, v_xs_1131_, v_fallback_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_00_u03b2_1135_, lean_object* v_inst_1136_, lean_object* v_xs_1137_, lean_object* v_fallback_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Std_Internal_List_minKeyD(v_00_u03b1_1134_, v_00_u03b2_1135_, v_inst_1136_, v_xs_1137_, v_fallback_1138_);
lean_dec(v_fallback_1138_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f___redArg(lean_object* v_inst_1140_, lean_object* v_xs_1141_){
_start:
{
lean_object* v___f_1142_; lean_object* v___x_1143_; 
v___f_1142_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1142_, 0, v_inst_1140_);
v___x_1143_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1142_, v_xs_1141_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f(lean_object* v_00_u03b1_1144_, lean_object* v_00_u03b2_1145_, lean_object* v_inst_1146_, lean_object* v_xs_1147_){
_start:
{
lean_object* v___f_1148_; lean_object* v___x_1149_; 
v___f_1148_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1148_, 0, v_inst_1146_);
v___x_1149_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1148_, v_xs_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey___redArg(lean_object* v_inst_1150_, lean_object* v_xs_1151_){
_start:
{
lean_object* v___f_1152_; lean_object* v___x_1153_; 
v___f_1152_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1152_, 0, v_inst_1150_);
v___x_1153_ = l_Std_Internal_List_minKey___redArg(v___f_1152_, v_xs_1151_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey(lean_object* v_00_u03b1_1154_, lean_object* v_00_u03b2_1155_, lean_object* v_inst_1156_, lean_object* v_xs_1157_, lean_object* v_h_1158_){
_start:
{
lean_object* v___f_1159_; lean_object* v___x_1160_; 
v___f_1159_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1159_, 0, v_inst_1156_);
v___x_1160_ = l_Std_Internal_List_minKey___redArg(v___f_1159_, v_xs_1157_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg(lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_xs_1163_){
_start:
{
lean_object* v___f_1164_; lean_object* v___x_1165_; 
v___f_1164_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1164_, 0, v_inst_1161_);
v___x_1165_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1164_, v_xs_1163_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_1167_ = l_panic___redArg(v_inst_1162_, v___x_1166_);
return v___x_1167_;
}
else
{
lean_object* v_val_1168_; 
v_val_1168_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v___x_1165_, 1);
return v_val_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg___boxed(lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_xs_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_1169_, v_inst_1170_, v_xs_1171_);
lean_dec(v_inst_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21(lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_xs_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_1175_, v_inst_1176_, v_xs_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_00_u03b2_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_xs_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_Internal_List_maxKey_x21(v_00_u03b1_1179_, v_00_u03b2_1180_, v_inst_1181_, v_inst_1182_, v_xs_1183_);
lean_dec(v_inst_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg(lean_object* v_inst_1185_, lean_object* v_xs_1186_, lean_object* v_fallback_1187_){
_start:
{
lean_object* v___f_1188_; lean_object* v___x_1189_; 
v___f_1188_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1188_, 0, v_inst_1185_);
v___x_1189_ = l_Std_Internal_List_minKeyD___redArg(v___f_1188_, v_xs_1186_, v_fallback_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg___boxed(lean_object* v_inst_1190_, lean_object* v_xs_1191_, lean_object* v_fallback_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_Internal_List_maxKeyD___redArg(v_inst_1190_, v_xs_1191_, v_fallback_1192_);
lean_dec(v_fallback_1192_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_inst_1196_, lean_object* v_xs_1197_, lean_object* v_fallback_1198_){
_start:
{
lean_object* v___f_1199_; lean_object* v___x_1200_; 
v___f_1199_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1199_, 0, v_inst_1196_);
v___x_1200_ = l_Std_Internal_List_minKeyD___redArg(v___f_1199_, v_xs_1197_, v_fallback_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___boxed(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_inst_1203_, lean_object* v_xs_1204_, lean_object* v_fallback_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Std_Internal_List_maxKeyD(v_00_u03b1_1201_, v_00_u03b2_1202_, v_inst_1203_, v_xs_1204_, v_fallback_1205_);
lean_dec(v_fallback_1205_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn___redArg(lean_object* v_inst_1207_, lean_object* v_l_1208_, lean_object* v_sofar_1209_, lean_object* v_k_1210_){
_start:
{
lean_object* v___x_1211_; 
lean_inc_ref(v_inst_1207_);
v___x_1211_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_1207_, v_k_1210_, v_l_1208_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_dec_ref(v_inst_1207_);
return v_sofar_1209_;
}
else
{
lean_object* v_val_1212_; lean_object* v_fst_1213_; lean_object* v_snd_1214_; lean_object* v___x_1215_; 
v_val_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_val_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v_fst_1213_ = lean_ctor_get(v_val_1212_, 0);
lean_inc(v_fst_1213_);
v_snd_1214_ = lean_ctor_get(v_val_1212_, 1);
lean_inc(v_snd_1214_);
lean_dec(v_val_1212_);
v___x_1215_ = l_Std_Internal_List_insertEntry___redArg(v_inst_1207_, v_fst_1213_, v_snd_1214_, v_sofar_1209_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn(lean_object* v_00_u03b1_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_inst_1218_, lean_object* v_l_1219_, lean_object* v_sofar_1220_, lean_object* v_k_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Std_Internal_List_interSmallerFn___redArg(v_inst_1218_, v_l_1219_, v_sofar_1220_, v_k_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_1223_, lean_object* v_h__1_1224_, lean_object* v_h__2_1225_){
_start:
{
if (lean_obj_tag(v_x_1223_) == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec(v_h__1_1224_);
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_apply_1(v_h__2_1225_, v___x_1226_);
return v___x_1227_;
}
else
{
lean_object* v_val_1228_; lean_object* v___x_1229_; 
lean_dec(v_h__2_1225_);
v_val_1228_ = lean_ctor_get(v_x_1223_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v_x_1223_, 1);
v___x_1229_ = lean_apply_1(v_h__1_1224_, v_val_1228_);
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_1230_, lean_object* v_00_u03b2_1231_, lean_object* v_motive_1232_, lean_object* v_x_1233_, lean_object* v_h__1_1234_, lean_object* v_h__2_1235_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_dec(v_h__1_1234_);
v___x_1236_ = lean_box(0);
v___x_1237_ = lean_apply_1(v_h__2_1235_, v___x_1236_);
return v___x_1237_;
}
else
{
lean_object* v_val_1238_; lean_object* v___x_1239_; 
lean_dec(v_h__2_1235_);
v_val_1238_ = lean_ctor_get(v_x_1233_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v_x_1233_, 1);
v___x_1239_ = lean_apply_1(v_h__1_1234_, v_val_1238_);
return v___x_1239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg___lam__0(lean_object* v_inst_1240_, lean_object* v_l_u2081_1241_, lean_object* v_sofar_1242_, lean_object* v_kv_1243_){
_start:
{
lean_object* v_fst_1244_; lean_object* v___x_1245_; 
v_fst_1244_ = lean_ctor_get(v_kv_1243_, 0);
lean_inc(v_fst_1244_);
lean_dec_ref(v_kv_1243_);
v___x_1245_ = l_Std_Internal_List_interSmallerFn___redArg(v_inst_1240_, v_l_u2081_1241_, v_sofar_1242_, v_fst_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg(lean_object* v_inst_1246_, lean_object* v_l_u2081_1247_, lean_object* v_l_u2082_1248_){
_start:
{
lean_object* v___f_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___f_1249_ = lean_alloc_closure((void*)(l_Std_Internal_List_interSmaller___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1249_, 0, v_inst_1246_);
lean_closure_set(v___f_1249_, 1, v_l_u2081_1247_);
v___x_1250_ = lean_box(0);
v___x_1251_ = l_List_foldl___redArg(v___f_1249_, v___x_1250_, v_l_u2082_1248_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller(lean_object* v_00_u03b1_1252_, lean_object* v_00_u03b2_1253_, lean_object* v_inst_1254_, lean_object* v_l_u2081_1255_, lean_object* v_l_u2082_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_Internal_List_interSmaller___redArg(v_inst_1254_, v_l_u2081_1255_, v_l_u2082_1256_);
return v___x_1257_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Internal_List_Associative(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
