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
uint8_t l_Std_Internal_List_beqModel___redArg___lam__0(lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_l_u2082_126_, lean_object* v_x_127_){
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
LEAN_EXPORT void l_Std_Internal_List_beqModel___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_124_ = stack[0].m_obj;
lean_object* v_inst_125_ = stack[1].m_obj;
lean_object* v_l_u2082_126_ = stack[2].m_obj;
lean_object* v_x_127_ = stack[3].m_obj;
uint8_t v_res_134_;
v_res_134_ = l_Std_Internal_List_beqModel___redArg___lam__0(v_inst_124_, v_inst_125_, v_l_u2082_126_, v_x_127_);
stack->m_num = v_res_134_;
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___lam__0___boxed(lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_l_u2082_137_, lean_object* v_x_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Std_Internal_List_beqModel___redArg___lam__0(v_inst_135_, v_inst_136_, v_l_u2082_137_, v_x_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
uint8_t l_Std_Internal_List_beqModel___redArg(lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_l_u2081_143_, lean_object* v_l_u2082_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_145_ = l_List_lengthTR___redArg(v_l_u2081_143_);
v___x_146_ = l_List_lengthTR___redArg(v_l_u2082_144_);
v___x_147_ = lean_nat_dec_eq(v___x_145_, v___x_146_);
lean_dec(v___x_146_);
lean_dec(v___x_145_);
if (v___x_147_ == 0)
{
lean_dec(v_l_u2082_144_);
lean_dec(v_l_u2081_143_);
lean_dec_ref(v_inst_142_);
lean_dec_ref(v_inst_141_);
return v___x_147_;
}
else
{
lean_object* v___f_148_; uint8_t v___x_149_; 
v___f_148_ = lean_alloc_closure((void*)(l_Std_Internal_List_beqModel___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_148_, 0, v_inst_142_);
lean_closure_set(v___f_148_, 1, v_inst_141_);
lean_closure_set(v___f_148_, 2, v_l_u2082_144_);
v___x_149_ = l_List_all___redArg(v_l_u2081_143_, v___f_148_);
return v___x_149_;
}
}
}
LEAN_EXPORT void l_Std_Internal_List_beqModel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_141_ = stack[0].m_obj;
lean_object* v_inst_142_ = stack[1].m_obj;
lean_object* v_l_u2081_143_ = stack[2].m_obj;
lean_object* v_l_u2082_144_ = stack[3].m_obj;
uint8_t v_res_150_;
v_res_150_ = l_Std_Internal_List_beqModel___redArg(v_inst_141_, v_inst_142_, v_l_u2081_143_, v_l_u2082_144_);
stack->m_num = v_res_150_;
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___redArg___boxed(lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_l_u2081_153_, lean_object* v_l_u2082_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Std_Internal_List_beqModel___redArg(v_inst_151_, v_inst_152_, v_l_u2081_153_, v_l_u2082_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
uint8_t l_Std_Internal_List_beqModel(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_l_u2081_162_, lean_object* v_l_u2082_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = l_Std_Internal_List_beqModel___redArg(v_inst_159_, v_inst_161_, v_l_u2081_162_, v_l_u2082_163_);
return v___x_164_;
}
}
LEAN_EXPORT void l_Std_Internal_List_beqModel_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_159_ = stack[2].m_obj;
lean_object* v_inst_161_ = stack[4].m_obj;
lean_object* v_l_u2081_162_ = stack[5].m_obj;
lean_object* v_l_u2082_163_ = stack[6].m_obj;
uint8_t v_res_165_;
v_res_165_ = l_Std_Internal_List_beqModel(lean_box(0), lean_box(0), v_inst_159_, lean_box(0), v_inst_161_, v_l_u2081_162_, v_l_u2082_163_);
stack->m_num = v_res_165_;
}
LEAN_EXPORT lean_object* l_Std_Internal_List_beqModel___boxed(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_l_u2081_171_, lean_object* v_l_u2082_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Std_Internal_List_beqModel(v_00_u03b1_166_, v_00_u03b2_167_, v_inst_168_, v_inst_169_, v_inst_170_, v_l_u2081_171_, v_l_u2082_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
uint8_t l_Std_Internal_List_Const_beqModel___redArg___lam__0(lean_object* v_inst_175_, lean_object* v_l_u2082_176_, lean_object* v_inst_177_, lean_object* v_x_178_){
_start:
{
lean_object* v_fst_179_; lean_object* v_snd_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_fst_179_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_fst_179_);
v_snd_180_ = lean_ctor_get(v_x_178_, 1);
lean_inc(v_snd_180_);
lean_dec_ref(v_x_178_);
v___x_181_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_175_, v_fst_179_, v_l_u2082_176_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_snd_180_);
v___x_183_ = l_instBEqOption_beq___redArg(v_inst_177_, v___x_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT void l_Std_Internal_List_Const_beqModel___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_175_ = stack[0].m_obj;
lean_object* v_l_u2082_176_ = stack[1].m_obj;
lean_object* v_inst_177_ = stack[2].m_obj;
lean_object* v_x_178_ = stack[3].m_obj;
uint8_t v_res_184_;
v_res_184_ = l_Std_Internal_List_Const_beqModel___redArg___lam__0(v_inst_175_, v_l_u2082_176_, v_inst_177_, v_x_178_);
stack->m_num = v_res_184_;
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed(lean_object* v_inst_185_, lean_object* v_l_u2082_186_, lean_object* v_inst_187_, lean_object* v_x_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Std_Internal_List_Const_beqModel___redArg___lam__0(v_inst_185_, v_l_u2082_186_, v_inst_187_, v_x_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
uint8_t l_Std_Internal_List_Const_beqModel___redArg(lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_l_u2081_193_, lean_object* v_l_u2082_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = l_List_lengthTR___redArg(v_l_u2081_193_);
v___x_196_ = l_List_lengthTR___redArg(v_l_u2082_194_);
v___x_197_ = lean_nat_dec_eq(v___x_195_, v___x_196_);
lean_dec(v___x_196_);
lean_dec(v___x_195_);
if (v___x_197_ == 0)
{
lean_dec(v_l_u2082_194_);
lean_dec(v_l_u2081_193_);
lean_dec_ref(v_inst_192_);
lean_dec_ref(v_inst_191_);
return v___x_197_;
}
else
{
lean_object* v___f_198_; uint8_t v___x_199_; 
v___f_198_ = lean_alloc_closure((void*)(l_Std_Internal_List_Const_beqModel___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_198_, 0, v_inst_191_);
lean_closure_set(v___f_198_, 1, v_l_u2082_194_);
lean_closure_set(v___f_198_, 2, v_inst_192_);
v___x_199_ = l_List_all___redArg(v_l_u2081_193_, v___f_198_);
return v___x_199_;
}
}
}
LEAN_EXPORT void l_Std_Internal_List_Const_beqModel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_191_ = stack[0].m_obj;
lean_object* v_inst_192_ = stack[1].m_obj;
lean_object* v_l_u2081_193_ = stack[2].m_obj;
lean_object* v_l_u2082_194_ = stack[3].m_obj;
uint8_t v_res_200_;
v_res_200_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_191_, v_inst_192_, v_l_u2081_193_, v_l_u2082_194_);
stack->m_num = v_res_200_;
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___redArg___boxed(lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_l_u2081_203_, lean_object* v_l_u2082_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_201_, v_inst_202_, v_l_u2081_203_, v_l_u2082_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
uint8_t l_Std_Internal_List_Const_beqModel(lean_object* v_00_u03b1_207_, lean_object* v_00_u03b2_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_l_u2081_211_, lean_object* v_l_u2082_212_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = l_Std_Internal_List_Const_beqModel___redArg(v_inst_209_, v_inst_210_, v_l_u2081_211_, v_l_u2082_212_);
return v___x_213_;
}
}
LEAN_EXPORT void l_Std_Internal_List_Const_beqModel_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_209_ = stack[2].m_obj;
lean_object* v_inst_210_ = stack[3].m_obj;
lean_object* v_l_u2081_211_ = stack[4].m_obj;
lean_object* v_l_u2082_212_ = stack[5].m_obj;
uint8_t v_res_214_;
v_res_214_ = l_Std_Internal_List_Const_beqModel(lean_box(0), lean_box(0), v_inst_209_, v_inst_210_, v_l_u2081_211_, v_l_u2082_212_);
stack->m_num = v_res_214_;
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_beqModel___boxed(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_l_u2081_219_, lean_object* v_l_u2082_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Std_Internal_List_Const_beqModel(v_00_u03b1_215_, v_00_u03b2_216_, v_inst_217_, v_inst_218_, v_l_u2081_219_, v_l_u2082_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
lean_object* v___x_225_; 
lean_dec(v_x_224_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
else
{
lean_object* v_val_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
v_val_226_ = lean_ctor_get(v_x_223_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v_x_223_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_val_226_);
lean_dec(v_x_223_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_apply_2(v_x_224_, v_val_226_, lean_box(0));
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___redArg(v_x_237_, v_x_238_);
return v___x_239_;
}
}
uint8_t l_Std_Internal_List_containsKey___redArg(lean_object* v_inst_240_, lean_object* v_a_241_, lean_object* v_x_242_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
uint8_t v___x_243_; 
lean_dec(v_a_241_);
lean_dec_ref(v_inst_240_);
v___x_243_ = 0;
return v___x_243_;
}
else
{
lean_object* v_head_244_; lean_object* v_tail_245_; lean_object* v_fst_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_head_244_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_head_244_);
v_tail_245_ = lean_ctor_get(v_x_242_, 1);
lean_inc(v_tail_245_);
lean_dec_ref_known(v_x_242_, 2);
v_fst_246_ = lean_ctor_get(v_head_244_, 0);
lean_inc(v_fst_246_);
lean_dec(v_head_244_);
lean_inc_ref(v_inst_240_);
lean_inc(v_a_241_);
v___x_247_ = lean_apply_2(v_inst_240_, v_fst_246_, v_a_241_);
v___x_248_ = lean_unbox(v___x_247_);
if (v___x_248_ == 0)
{
v_x_242_ = v_tail_245_;
goto _start;
}
else
{
uint8_t v___x_250_; 
lean_dec(v_tail_245_);
lean_dec(v_a_241_);
lean_dec_ref(v_inst_240_);
v___x_250_ = lean_unbox(v___x_247_);
return v___x_250_;
}
}
}
}
LEAN_EXPORT void l_Std_Internal_List_containsKey___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_240_ = stack[0].m_obj;
lean_object* v_a_241_ = stack[1].m_obj;
lean_object* v_x_242_ = stack[2].m_obj;
uint8_t v_res_251_;
v_res_251_ = l_Std_Internal_List_containsKey___redArg(v_inst_240_, v_a_241_, v_x_242_);
stack->m_num = v_res_251_;
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___redArg___boxed(lean_object* v_inst_252_, lean_object* v_a_253_, lean_object* v_x_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Std_Internal_List_containsKey___redArg(v_inst_252_, v_a_253_, v_x_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
uint8_t l_Std_Internal_List_containsKey(lean_object* v_00_u03b1_257_, lean_object* v_00_u03b2_258_, lean_object* v_inst_259_, lean_object* v_a_260_, lean_object* v_x_261_){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = l_Std_Internal_List_containsKey___redArg(v_inst_259_, v_a_260_, v_x_261_);
return v___x_262_;
}
}
LEAN_EXPORT void l_Std_Internal_List_containsKey_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_259_ = stack[2].m_obj;
lean_object* v_a_260_ = stack[3].m_obj;
lean_object* v_x_261_ = stack[4].m_obj;
uint8_t v_res_263_;
v_res_263_ = l_Std_Internal_List_containsKey(lean_box(0), lean_box(0), v_inst_259_, v_a_260_, v_x_261_);
stack->m_num = v_res_263_;
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___boxed(lean_object* v_00_u03b1_264_, lean_object* v_00_u03b2_265_, lean_object* v_inst_266_, lean_object* v_a_267_, lean_object* v_x_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Std_Internal_List_containsKey(v_00_u03b1_264_, v_00_u03b2_265_, v_inst_266_, v_a_267_, v_x_268_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry___redArg(lean_object* v_inst_271_, lean_object* v_a_272_, lean_object* v_l_273_){
_start:
{
lean_object* v___x_274_; lean_object* v_val_275_; 
v___x_274_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_271_, v_a_272_, v_l_273_);
v_val_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_val_275_);
lean_dec(v___x_274_);
return v_val_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_, lean_object* v_inst_278_, lean_object* v_a_279_, lean_object* v_l_280_, lean_object* v_h_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_Internal_List_getEntry___redArg(v_inst_278_, v_a_279_, v_l_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue___redArg(lean_object* v_inst_283_, lean_object* v_a_284_, lean_object* v_l_285_){
_start:
{
lean_object* v___x_286_; lean_object* v_val_287_; 
v___x_286_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_283_, v_a_284_, v_l_285_);
v_val_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_287_);
lean_dec(v___x_286_);
return v_val_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue(lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_inst_290_, lean_object* v_a_291_, lean_object* v_l_292_, lean_object* v_h_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_Internal_List_getValue___redArg(v_inst_290_, v_a_291_, v_l_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast___redArg(lean_object* v_inst_295_, lean_object* v_a_296_, lean_object* v_l_297_){
_start:
{
lean_object* v___x_298_; lean_object* v_val_299_; 
v___x_298_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_295_, v_a_296_, v_l_297_);
v_val_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_val_299_);
lean_dec(v___x_298_);
return v_val_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast(lean_object* v_00_u03b1_300_, lean_object* v_00_u03b2_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_a_304_, lean_object* v_l_305_, lean_object* v_h_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Std_Internal_List_getValueCast___redArg(v_inst_302_, v_a_304_, v_l_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg(lean_object* v_inst_308_, lean_object* v_a_309_, lean_object* v_l_310_, lean_object* v_fallback_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_308_, v_a_309_, v_l_310_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_inc(v_fallback_311_);
return v_fallback_311_;
}
else
{
lean_object* v_val_313_; 
v_val_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_313_);
lean_dec_ref_known(v___x_312_, 1);
return v_val_313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___redArg___boxed(lean_object* v_inst_314_, lean_object* v_a_315_, lean_object* v_l_316_, lean_object* v_fallback_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_Internal_List_getValueCastD___redArg(v_inst_314_, v_a_315_, v_l_316_, v_fallback_317_);
lean_dec(v_fallback_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD(lean_object* v_00_u03b1_319_, lean_object* v_00_u03b2_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_a_323_, lean_object* v_l_324_, lean_object* v_fallback_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_Internal_List_getValueCastD___redArg(v_inst_321_, v_a_323_, v_l_324_, v_fallback_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___boxed(lean_object* v_00_u03b1_327_, lean_object* v_00_u03b2_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_a_331_, lean_object* v_l_332_, lean_object* v_fallback_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_Internal_List_getValueCastD(v_00_u03b1_327_, v_00_u03b2_328_, v_inst_329_, v_inst_330_, v_a_331_, v_l_332_, v_fallback_333_);
lean_dec(v_fallback_333_);
return v_res_334_;
}
}
static lean_object* _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_338_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__2));
v___x_339_ = lean_unsigned_to_nat(14u);
v___x_340_ = lean_unsigned_to_nat(22u);
v___x_341_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__1));
v___x_342_ = ((lean_object*)(l_Std_Internal_List_getValueCast_x21___redArg___closed__0));
v___x_343_ = l_mkPanicMessageWithDecl(v___x_342_, v___x_341_, v___x_340_, v___x_339_, v___x_338_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___redArg(lean_object* v_inst_344_, lean_object* v_a_345_, lean_object* v_inst_346_, lean_object* v_l_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_344_, v_a_345_, v_l_347_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_350_ = l_panic___redArg(v_inst_346_, v___x_349_);
return v___x_350_;
}
else
{
lean_object* v_val_351_; 
v_val_351_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_val_351_);
lean_dec_ref_known(v___x_348_, 1);
return v_val_351_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___redArg___boxed(lean_object* v_inst_352_, lean_object* v_a_353_, lean_object* v_inst_354_, lean_object* v_l_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_Internal_List_getValueCast_x21___redArg(v_inst_352_, v_a_353_, v_inst_354_, v_l_355_);
lean_dec(v_inst_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21(lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_a_361_, lean_object* v_inst_362_, lean_object* v_l_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_Internal_List_getValueCast_x21___redArg(v_inst_359_, v_a_361_, v_inst_362_, v_l_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___boxed(lean_object* v_00_u03b1_365_, lean_object* v_00_u03b2_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_a_369_, lean_object* v_inst_370_, lean_object* v_l_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_Internal_List_getValueCast_x21(v_00_u03b1_365_, v_00_u03b2_366_, v_inst_367_, v_inst_368_, v_a_369_, v_inst_370_, v_l_371_);
lean_dec(v_inst_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg(lean_object* v_inst_373_, lean_object* v_a_374_, lean_object* v_l_375_, lean_object* v_fallback_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_373_, v_a_374_, v_l_375_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_inc(v_fallback_376_);
return v_fallback_376_;
}
else
{
lean_object* v_val_378_; 
v_val_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_val_378_);
lean_dec_ref_known(v___x_377_, 1);
return v_val_378_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___redArg___boxed(lean_object* v_inst_379_, lean_object* v_a_380_, lean_object* v_l_381_, lean_object* v_fallback_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Internal_List_getValueD___redArg(v_inst_379_, v_a_380_, v_l_381_, v_fallback_382_);
lean_dec(v_fallback_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD(lean_object* v_00_u03b1_384_, lean_object* v_00_u03b2_385_, lean_object* v_inst_386_, lean_object* v_a_387_, lean_object* v_l_388_, lean_object* v_fallback_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_Internal_List_getValueD___redArg(v_inst_386_, v_a_387_, v_l_388_, v_fallback_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___boxed(lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_inst_393_, lean_object* v_a_394_, lean_object* v_l_395_, lean_object* v_fallback_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_Internal_List_getValueD(v_00_u03b1_391_, v_00_u03b2_392_, v_inst_393_, v_a_394_, v_l_395_, v_fallback_396_);
lean_dec(v_fallback_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg(lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_a_400_, lean_object* v_l_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_398_, v_a_400_, v_l_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_404_ = l_panic___redArg(v_inst_399_, v___x_403_);
return v___x_404_;
}
else
{
lean_object* v_val_405_; 
v_val_405_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v___x_402_, 1);
return v_val_405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___redArg___boxed(lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_a_408_, lean_object* v_l_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_Internal_List_getValue_x21___redArg(v_inst_406_, v_inst_407_, v_a_408_, v_l_409_);
lean_dec(v_inst_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21(lean_object* v_00_u03b1_411_, lean_object* v_00_u03b2_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_a_415_, lean_object* v_l_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_Internal_List_getValue_x21___redArg(v_inst_413_, v_inst_414_, v_a_415_, v_l_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___boxed(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_a_422_, lean_object* v_l_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_Internal_List_getValue_x21(v_00_u03b1_418_, v_00_u03b2_419_, v_inst_420_, v_inst_421_, v_a_422_, v_l_423_);
lean_dec(v_inst_421_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f___redArg(lean_object* v_inst_425_, lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
lean_object* v___x_428_; 
lean_dec(v_a_426_);
lean_dec_ref(v_inst_425_);
v___x_428_ = lean_box(0);
return v___x_428_;
}
else
{
lean_object* v_head_429_; lean_object* v_tail_430_; lean_object* v_fst_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_head_429_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_head_429_);
v_tail_430_ = lean_ctor_get(v_x_427_, 1);
lean_inc(v_tail_430_);
lean_dec_ref_known(v_x_427_, 2);
v_fst_431_ = lean_ctor_get(v_head_429_, 0);
lean_inc_n(v_fst_431_, 2);
lean_dec(v_head_429_);
lean_inc_ref(v_inst_425_);
lean_inc(v_a_426_);
v___x_432_ = lean_apply_2(v_inst_425_, v_fst_431_, v_a_426_);
v___x_433_ = lean_unbox(v___x_432_);
if (v___x_433_ == 0)
{
lean_dec(v_fst_431_);
v_x_427_ = v_tail_430_;
goto _start;
}
else
{
lean_object* v___x_435_; 
lean_dec(v_tail_430_);
lean_dec(v_a_426_);
lean_dec_ref(v_inst_425_);
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v_fst_431_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_inst_438_, lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_438_, v_a_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey___redArg(lean_object* v_inst_442_, lean_object* v_a_443_, lean_object* v_l_444_){
_start:
{
lean_object* v___x_445_; lean_object* v_val_446_; 
v___x_445_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_442_, v_a_443_, v_l_444_);
v_val_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_val_446_);
lean_dec(v___x_445_);
return v_val_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey(lean_object* v_00_u03b1_447_, lean_object* v_00_u03b2_448_, lean_object* v_inst_449_, lean_object* v_a_450_, lean_object* v_l_451_, lean_object* v_h_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_Internal_List_getKey___redArg(v_inst_449_, v_a_450_, v_l_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg(lean_object* v_inst_454_, lean_object* v_a_455_, lean_object* v_l_456_, lean_object* v_fallback_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_454_, v_a_455_, v_l_456_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_inc(v_fallback_457_);
return v_fallback_457_;
}
else
{
lean_object* v_val_459_; 
v_val_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_val_459_);
lean_dec_ref_known(v___x_458_, 1);
return v_val_459_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___redArg___boxed(lean_object* v_inst_460_, lean_object* v_a_461_, lean_object* v_l_462_, lean_object* v_fallback_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_Internal_List_getKeyD___redArg(v_inst_460_, v_a_461_, v_l_462_, v_fallback_463_);
lean_dec(v_fallback_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD(lean_object* v_00_u03b1_465_, lean_object* v_00_u03b2_466_, lean_object* v_inst_467_, lean_object* v_a_468_, lean_object* v_l_469_, lean_object* v_fallback_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_Internal_List_getKeyD___redArg(v_inst_467_, v_a_468_, v_l_469_, v_fallback_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___boxed(lean_object* v_00_u03b1_472_, lean_object* v_00_u03b2_473_, lean_object* v_inst_474_, lean_object* v_a_475_, lean_object* v_l_476_, lean_object* v_fallback_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_Internal_List_getKeyD(v_00_u03b1_472_, v_00_u03b2_473_, v_inst_474_, v_a_475_, v_l_476_, v_fallback_477_);
lean_dec(v_fallback_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg(lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_a_481_, lean_object* v_l_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_Internal_List_getKey_x3f___redArg(v_inst_479_, v_a_481_, v_l_482_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_485_ = l_panic___redArg(v_inst_480_, v___x_484_);
return v___x_485_;
}
else
{
lean_object* v_val_486_; 
v_val_486_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v___x_483_, 1);
return v_val_486_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___redArg___boxed(lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_a_489_, lean_object* v_l_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_Internal_List_getKey_x21___redArg(v_inst_487_, v_inst_488_, v_a_489_, v_l_490_);
lean_dec(v_inst_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_a_496_, lean_object* v_l_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_Internal_List_getKey_x21___redArg(v_inst_494_, v_inst_495_, v_a_496_, v_l_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___boxed(lean_object* v_00_u03b1_499_, lean_object* v_00_u03b2_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_a_503_, lean_object* v_l_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_Internal_List_getKey_x21(v_00_u03b1_499_, v_00_u03b2_500_, v_inst_501_, v_inst_502_, v_a_503_, v_l_504_);
lean_dec(v_inst_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry___redArg(lean_object* v_inst_506_, lean_object* v_k_507_, lean_object* v_v_508_, lean_object* v_x_509_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
lean_object* v___x_510_; 
lean_dec(v_v_508_);
lean_dec(v_k_507_);
lean_dec_ref(v_inst_506_);
v___x_510_ = lean_box(0);
return v___x_510_;
}
else
{
lean_object* v_head_511_; lean_object* v_tail_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_535_; 
v_head_511_ = lean_ctor_get(v_x_509_, 0);
v_tail_512_ = lean_ctor_get(v_x_509_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v_x_509_);
if (v_isSharedCheck_535_ == 0)
{
v___x_514_ = v_x_509_;
v_isShared_515_ = v_isSharedCheck_535_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_tail_512_);
lean_inc(v_head_511_);
lean_dec(v_x_509_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_535_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_fst_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_fst_516_ = lean_ctor_get(v_head_511_, 0);
lean_inc_ref(v_inst_506_);
lean_inc(v_k_507_);
lean_inc(v_fst_516_);
v___x_517_ = lean_apply_2(v_inst_506_, v_fst_516_, v_k_507_);
v___x_518_ = lean_unbox(v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_506_, v_k_507_, v_v_508_, v_tail_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_519_);
v___x_521_ = v___x_514_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_head_511_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
else
{
lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_532_; 
lean_dec_ref(v_inst_506_);
v_isSharedCheck_532_ = !lean_is_exclusive(v_head_511_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; lean_object* v_unused_534_; 
v_unused_533_ = lean_ctor_get(v_head_511_, 1);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_head_511_, 0);
lean_dec(v_unused_534_);
v___x_524_ = v_head_511_;
v_isShared_525_ = v_isSharedCheck_532_;
goto v_resetjp_523_;
}
else
{
lean_dec(v_head_511_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_532_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v_v_508_);
lean_ctor_set(v___x_524_, 0, v_k_507_);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_v_508_);
v___x_527_ = v_reuseFailAlloc_531_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_529_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_527_);
v___x_529_ = v___x_514_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_tail_512_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_inst_538_, lean_object* v_k_539_, lean_object* v_v_540_, lean_object* v_x_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_538_, v_k_539_, v_v_540_, v_x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey___redArg(lean_object* v_inst_543_, lean_object* v_k_544_, lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v___x_546_; 
lean_dec(v_k_544_);
lean_dec_ref(v_inst_543_);
v___x_546_ = lean_box(0);
return v___x_546_;
}
else
{
lean_object* v_head_547_; lean_object* v_tail_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_559_; 
v_head_547_ = lean_ctor_get(v_x_545_, 0);
v_tail_548_ = lean_ctor_get(v_x_545_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_559_ == 0)
{
v___x_550_ = v_x_545_;
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_tail_548_);
lean_inc(v_head_547_);
lean_dec(v_x_545_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_fst_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_fst_552_ = lean_ctor_get(v_head_547_, 0);
lean_inc_ref(v_inst_543_);
lean_inc(v_k_544_);
lean_inc(v_fst_552_);
v___x_553_ = lean_apply_2(v_inst_543_, v_fst_552_, v_k_544_);
v___x_554_ = lean_unbox(v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = l_Std_Internal_List_eraseKey___redArg(v_inst_543_, v_k_544_, v_tail_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_555_);
v___x_557_ = v___x_550_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_head_547_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
else
{
lean_del_object(v___x_550_);
lean_dec(v_head_547_);
lean_dec(v_k_544_);
lean_dec_ref(v_inst_543_);
return v_tail_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey(lean_object* v_00_u03b1_560_, lean_object* v_00_u03b2_561_, lean_object* v_inst_562_, lean_object* v_k_563_, lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_Internal_List_eraseKey___redArg(v_inst_562_, v_k_563_, v_x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry___redArg(lean_object* v_inst_566_, lean_object* v_k_567_, lean_object* v_v_568_, lean_object* v_l_569_){
_start:
{
uint8_t v___x_570_; 
lean_inc(v_l_569_);
lean_inc(v_k_567_);
lean_inc_ref(v_inst_566_);
v___x_570_ = l_Std_Internal_List_containsKey___redArg(v_inst_566_, v_k_567_, v_l_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec_ref(v_inst_566_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_k_567_);
lean_ctor_set(v___x_571_, 1, v_v_568_);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_l_569_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_566_, v_k_567_, v_v_568_, v_l_569_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry(lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_inst_576_, lean_object* v_k_577_, lean_object* v_v_578_, lean_object* v_l_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_Internal_List_insertEntry___redArg(v_inst_576_, v_k_577_, v_v_578_, v_l_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew___redArg(lean_object* v_inst_581_, lean_object* v_k_582_, lean_object* v_v_583_, lean_object* v_l_584_){
_start:
{
uint8_t v___x_585_; 
lean_inc(v_l_584_);
lean_inc(v_k_582_);
v___x_585_ = l_Std_Internal_List_containsKey___redArg(v_inst_581_, v_k_582_, v_l_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_k_582_);
lean_ctor_set(v___x_586_, 1, v_v_583_);
v___x_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_l_584_);
return v___x_587_;
}
else
{
lean_dec(v_v_583_);
lean_dec(v_k_582_);
return v_l_584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_inst_590_, lean_object* v_k_591_, lean_object* v_v_592_, lean_object* v_l_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_590_, v_k_591_, v_v_592_, v_l_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_595_, lean_object* v_h__1_596_, lean_object* v_h__2_597_){
_start:
{
if (lean_obj_tag(v_x_595_) == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_h__2_597_);
v___x_598_ = lean_box(0);
v___x_599_ = lean_apply_1(v_h__1_596_, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v_val_600_; lean_object* v___x_601_; 
lean_dec(v_h__1_596_);
v_val_600_ = lean_ctor_get(v_x_595_, 0);
lean_inc(v_val_600_);
lean_dec_ref_known(v_x_595_, 1);
v___x_601_ = lean_apply_1(v_h__2_597_, v_val_600_);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_602_, lean_object* v_motive_603_, lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_h__2_606_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_apply_1(v_h__1_605_, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v_val_609_; lean_object* v___x_610_; 
lean_dec(v_h__1_605_);
v_val_609_ = lean_ctor_get(v_x_604_, 0);
lean_inc(v_val_609_);
lean_dec_ref_known(v_x_604_, 1);
v___x_610_ = lean_apply_1(v_h__2_606_, v_val_609_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_611_, lean_object* v_h__1_612_, lean_object* v_h__2_613_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_615_; 
lean_dec(v_h__2_613_);
v_a_614_ = lean_ctor_get(v_x_611_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v_x_611_, 1);
v___x_615_ = lean_apply_1(v_h__1_612_, v_a_614_);
return v___x_615_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_617_; 
lean_dec(v_h__1_612_);
v_a_616_ = lean_ctor_get(v_x_611_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v_x_611_, 1);
v___x_617_ = lean_apply_1(v_h__2_613_, v_a_616_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_618_, lean_object* v_motive_619_, lean_object* v_x_620_, lean_object* v_h__1_621_, lean_object* v_h__2_622_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; 
lean_dec(v_h__2_622_);
v_a_623_ = lean_ctor_get(v_x_620_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v_x_620_, 1);
v___x_624_ = lean_apply_1(v_h__1_621_, v_a_623_);
return v___x_624_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_626_; 
lean_dec(v_h__1_621_);
v_a_625_ = lean_ctor_get(v_x_620_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v_x_620_, 1);
v___x_626_ = lean_apply_1(v_h__2_622_, v_a_625_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList___redArg(lean_object* v_inst_627_, lean_object* v_l_628_, lean_object* v_toInsert_629_){
_start:
{
if (lean_obj_tag(v_toInsert_629_) == 0)
{
lean_dec_ref(v_inst_627_);
return v_l_628_;
}
else
{
lean_object* v_head_630_; lean_object* v_tail_631_; lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_634_; 
v_head_630_ = lean_ctor_get(v_toInsert_629_, 0);
lean_inc(v_head_630_);
v_tail_631_ = lean_ctor_get(v_toInsert_629_, 1);
lean_inc(v_tail_631_);
lean_dec_ref_known(v_toInsert_629_, 2);
v_fst_632_ = lean_ctor_get(v_head_630_, 0);
lean_inc(v_fst_632_);
v_snd_633_ = lean_ctor_get(v_head_630_, 1);
lean_inc(v_snd_633_);
lean_dec(v_head_630_);
lean_inc_ref(v_inst_627_);
v___x_634_ = l_Std_Internal_List_insertEntry___redArg(v_inst_627_, v_fst_632_, v_snd_633_, v_l_628_);
v_l_628_ = v___x_634_;
v_toInsert_629_ = v_tail_631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList(lean_object* v_00_u03b1_636_, lean_object* v_00_u03b2_637_, lean_object* v_inst_638_, lean_object* v_l_639_, lean_object* v_toInsert_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_Internal_List_insertList___redArg(v_inst_638_, v_l_639_, v_toInsert_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_642_, lean_object* v_h__1_643_, lean_object* v_h__2_644_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v_h__2_644_);
v___x_645_ = lean_box(0);
v___x_646_ = lean_apply_1(v_h__1_643_, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v_head_647_; lean_object* v_tail_648_; lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v___x_651_; 
lean_dec(v_h__1_643_);
v_head_647_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_head_647_);
v_tail_648_ = lean_ctor_get(v_x_642_, 1);
lean_inc(v_tail_648_);
lean_dec_ref_known(v_x_642_, 2);
v_fst_649_ = lean_ctor_get(v_head_647_, 0);
lean_inc(v_fst_649_);
v_snd_650_ = lean_ctor_get(v_head_647_, 1);
lean_inc(v_snd_650_);
lean_dec(v_head_647_);
v___x_651_ = lean_apply_3(v_h__2_644_, v_fst_649_, v_snd_650_, v_tail_648_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_652_, lean_object* v_00_u03b2_653_, lean_object* v_motive_654_, lean_object* v_x_655_, lean_object* v_h__1_656_, lean_object* v_h__2_657_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v_h__2_657_);
v___x_658_ = lean_box(0);
v___x_659_ = lean_apply_1(v_h__1_656_, v___x_658_);
return v___x_659_;
}
else
{
lean_object* v_head_660_; lean_object* v_tail_661_; lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_664_; 
lean_dec(v_h__1_656_);
v_head_660_ = lean_ctor_get(v_x_655_, 0);
lean_inc(v_head_660_);
v_tail_661_ = lean_ctor_get(v_x_655_, 1);
lean_inc(v_tail_661_);
lean_dec_ref_known(v_x_655_, 2);
v_fst_662_ = lean_ctor_get(v_head_660_, 0);
lean_inc(v_fst_662_);
v_snd_663_ = lean_ctor_get(v_head_660_, 1);
lean_inc(v_snd_663_);
lean_dec(v_head_660_);
v___x_664_ = lean_apply_3(v_h__2_657_, v_fst_662_, v_snd_663_, v_tail_661_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew___redArg(lean_object* v_inst_665_, lean_object* v_l_666_, lean_object* v_toInsert_667_){
_start:
{
if (lean_obj_tag(v_toInsert_667_) == 0)
{
lean_dec_ref(v_inst_665_);
return v_l_666_;
}
else
{
lean_object* v_head_668_; lean_object* v_tail_669_; lean_object* v_fst_670_; lean_object* v_snd_671_; lean_object* v___x_672_; 
v_head_668_ = lean_ctor_get(v_toInsert_667_, 0);
lean_inc(v_head_668_);
v_tail_669_ = lean_ctor_get(v_toInsert_667_, 1);
lean_inc(v_tail_669_);
lean_dec_ref_known(v_toInsert_667_, 2);
v_fst_670_ = lean_ctor_get(v_head_668_, 0);
lean_inc(v_fst_670_);
v_snd_671_ = lean_ctor_get(v_head_668_, 1);
lean_inc(v_snd_671_);
lean_dec(v_head_668_);
lean_inc_ref(v_inst_665_);
v___x_672_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_665_, v_fst_670_, v_snd_671_, v_l_666_);
v_l_666_ = v___x_672_;
v_toInsert_667_ = v_tail_669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNew(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_inst_676_, lean_object* v_l_677_, lean_object* v_toInsert_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_Internal_List_insertListIfNew___redArg(v_inst_676_, v_l_677_, v_toInsert_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList___redArg(lean_object* v_inst_680_, lean_object* v_l_u2081_681_, lean_object* v_l_u2082_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = l_List_lengthTR___redArg(v_l_u2081_681_);
v___x_684_ = l_List_lengthTR___redArg(v_l_u2082_682_);
v___x_685_ = lean_nat_dec_le(v___x_683_, v___x_684_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_Internal_List_insertList___redArg(v_inst_680_, v_l_u2081_681_, v_l_u2082_682_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_Internal_List_insertListIfNew___redArg(v_inst_680_, v_l_u2082_682_, v_l_u2081_681_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertSmallerList(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_inst_690_, lean_object* v_l_u2081_691_, lean_object* v_l_u2082_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_Internal_List_insertSmallerList___redArg(v_inst_690_, v_l_u2081_691_, v_l_u2082_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma___redArg(lean_object* v_p_694_){
_start:
{
lean_object* v_fst_695_; lean_object* v_snd_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_fst_695_ = lean_ctor_get(v_p_694_, 0);
v_snd_696_ = lean_ctor_get(v_p_694_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_p_694_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v_p_694_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_snd_696_);
lean_inc(v_fst_695_);
lean_dec(v_p_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_fst_695_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_snd_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma(lean_object* v_00_u03b1_704_, lean_object* v_00_u03b2_705_, lean_object* v_p_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_Internal_List_Prod_toSigma___redArg(v_p_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst___redArg(lean_object* v_inst_709_, lean_object* v_l_710_, lean_object* v_toInsert_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_712_ = ((lean_object*)(l_Std_Internal_List_insertListConst___redArg___closed__0));
v___x_713_ = lean_box(0);
v___x_714_ = l_List_mapTR_loop___redArg(v___x_712_, v_toInsert_711_, v___x_713_);
v___x_715_ = l_Std_Internal_List_insertList___redArg(v_inst_709_, v_l_710_, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst(lean_object* v_00_u03b1_716_, lean_object* v_00_u03b2_717_, lean_object* v_inst_718_, lean_object* v_l_719_, lean_object* v_toInsert_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Std_Internal_List_insertListConst___redArg(v_inst_718_, v_l_719_, v_toInsert_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit___redArg(lean_object* v_inst_722_, lean_object* v_l_723_, lean_object* v_toInsert_724_){
_start:
{
if (lean_obj_tag(v_toInsert_724_) == 0)
{
lean_dec_ref(v_inst_722_);
return v_l_723_;
}
else
{
lean_object* v_head_725_; lean_object* v_tail_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_head_725_ = lean_ctor_get(v_toInsert_724_, 0);
lean_inc(v_head_725_);
v_tail_726_ = lean_ctor_get(v_toInsert_724_, 1);
lean_inc(v_tail_726_);
lean_dec_ref_known(v_toInsert_724_, 2);
v___x_727_ = lean_box(0);
lean_inc_ref(v_inst_722_);
v___x_728_ = l_Std_Internal_List_insertEntryIfNew___redArg(v_inst_722_, v_head_725_, v___x_727_, v_l_723_);
v_l_723_ = v___x_728_;
v_toInsert_724_ = v_tail_726_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit(lean_object* v_00_u03b1_730_, lean_object* v_inst_731_, lean_object* v_l_732_, lean_object* v_toInsert_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_Internal_List_insertListIfNewUnit___redArg(v_inst_731_, v_l_732_, v_toInsert_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(lean_object* v_toInsert_735_, lean_object* v_h__1_736_, lean_object* v_h__2_737_){
_start:
{
if (lean_obj_tag(v_toInsert_735_) == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v_h__2_737_);
v___x_738_ = lean_box(0);
v___x_739_ = lean_apply_1(v_h__1_736_, v___x_738_);
return v___x_739_;
}
else
{
lean_object* v_head_740_; lean_object* v_tail_741_; lean_object* v___x_742_; 
lean_dec(v_h__1_736_);
v_head_740_ = lean_ctor_get(v_toInsert_735_, 0);
lean_inc(v_head_740_);
v_tail_741_ = lean_ctor_get(v_toInsert_735_, 1);
lean_inc(v_tail_741_);
lean_dec_ref_known(v_toInsert_735_, 2);
v___x_742_ = lean_apply_2(v_h__2_737_, v_head_740_, v_tail_741_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object* v_00_u03b1_743_, lean_object* v_motive_744_, lean_object* v_toInsert_745_, lean_object* v_h__1_746_, lean_object* v_h__2_747_){
_start:
{
if (lean_obj_tag(v_toInsert_745_) == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec(v_h__2_747_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_apply_1(v_h__1_746_, v___x_748_);
return v___x_749_;
}
else
{
lean_object* v_head_750_; lean_object* v_tail_751_; lean_object* v___x_752_; 
lean_dec(v_h__1_746_);
v_head_750_ = lean_ctor_get(v_toInsert_745_, 0);
lean_inc(v_head_750_);
v_tail_751_ = lean_ctor_get(v_toInsert_745_, 1);
lean_inc(v_tail_751_);
lean_dec_ref_known(v_toInsert_745_, 2);
v___x_752_ = lean_apply_2(v_h__2_747_, v_head_750_, v_tail_751_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey___redArg(lean_object* v_inst_753_, lean_object* v_k_754_, lean_object* v_f_755_, lean_object* v_l_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
lean_inc(v_l_756_);
lean_inc(v_k_754_);
lean_inc_ref(v_inst_753_);
v___x_757_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_753_, v_k_754_, v_l_756_);
v___x_758_ = lean_apply_1(v_f_755_, v___x_757_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_759_; 
v___x_759_ = l_Std_Internal_List_eraseKey___redArg(v_inst_753_, v_k_754_, v_l_756_);
return v___x_759_;
}
else
{
lean_object* v_val_760_; lean_object* v___x_761_; 
v_val_760_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v___x_758_, 1);
v___x_761_ = l_Std_Internal_List_insertEntry___redArg(v_inst_753_, v_k_754_, v_val_760_, v_l_756_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_k_766_, lean_object* v_f_767_, lean_object* v_l_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_Internal_List_alterKey___redArg(v_inst_764_, v_k_766_, v_f_767_, v_l_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___redArg(lean_object* v_x_770_, lean_object* v_h__1_771_, lean_object* v_h__2_772_){
_start:
{
if (lean_obj_tag(v_x_770_) == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec(v_h__2_772_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_apply_1(v_h__1_771_, v___x_773_);
return v___x_774_;
}
else
{
lean_object* v_val_775_; lean_object* v___x_776_; 
lean_dec(v_h__1_771_);
v_val_775_ = lean_ctor_get(v_x_770_, 0);
lean_inc(v_val_775_);
lean_dec_ref_known(v_x_770_, 1);
v___x_776_ = lean_apply_1(v_h__2_772_, v_val_775_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_k_779_, lean_object* v_motive_780_, lean_object* v_x_781_, lean_object* v_h__1_782_, lean_object* v_h__2_783_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec(v_h__2_783_);
v___x_784_ = lean_box(0);
v___x_785_ = lean_apply_1(v_h__1_782_, v___x_784_);
return v___x_785_;
}
else
{
lean_object* v_val_786_; lean_object* v___x_787_; 
lean_dec(v_h__1_782_);
v_val_786_ = lean_ctor_get(v_x_781_, 0);
lean_inc(v_val_786_);
lean_dec_ref_known(v_x_781_, 1);
v___x_787_ = lean_apply_1(v_h__2_783_, v_val_786_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* v_00_u03b1_788_, lean_object* v_00_u03b2_789_, lean_object* v_k_790_, lean_object* v_motive_791_, lean_object* v_x_792_, lean_object* v_h__1_793_, lean_object* v_h__2_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(v_00_u03b1_788_, v_00_u03b2_789_, v_k_790_, v_motive_791_, v_x_792_, v_h__1_793_, v_h__2_794_);
lean_dec(v_k_790_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_796_, lean_object* v_h__1_797_, lean_object* v_h__2_798_){
_start:
{
if (lean_obj_tag(v_x_796_) == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v_h__2_798_);
v___x_799_ = lean_box(0);
v___x_800_ = lean_apply_1(v_h__1_797_, v___x_799_);
return v___x_800_;
}
else
{
lean_object* v_val_801_; lean_object* v___x_802_; 
lean_dec(v_h__1_797_);
v_val_801_ = lean_ctor_get(v_x_796_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v_x_796_, 1);
v___x_802_ = lean_apply_1(v_h__2_798_, v_val_801_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_k_805_, lean_object* v_motive_806_, lean_object* v_x_807_, lean_object* v_h__1_808_, lean_object* v_h__2_809_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v_h__2_809_);
v___x_810_ = lean_box(0);
v___x_811_ = lean_apply_1(v_h__1_808_, v___x_810_);
return v___x_811_;
}
else
{
lean_object* v_val_812_; lean_object* v___x_813_; 
lean_dec(v_h__1_808_);
v_val_812_ = lean_ctor_get(v_x_807_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v_x_807_, 1);
v___x_813_ = lean_apply_1(v_h__2_809_, v_val_812_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter___boxed(lean_object* v_00_u03b1_814_, lean_object* v_00_u03b2_815_, lean_object* v_k_816_, lean_object* v_motive_817_, lean_object* v_x_818_, lean_object* v_h__1_819_, lean_object* v_h__2_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey__cons__perm_match__1_splitter(v_00_u03b1_814_, v_00_u03b2_815_, v_k_816_, v_motive_817_, v_x_818_, v_h__1_819_, v_h__2_820_);
lean_dec(v_k_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey___redArg(lean_object* v_inst_822_, lean_object* v_k_823_, lean_object* v_f_824_, lean_object* v_l_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_inc(v_l_825_);
lean_inc(v_k_823_);
lean_inc_ref(v_inst_822_);
v___x_826_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_822_, v_k_823_, v_l_825_);
v___x_827_ = lean_apply_1(v_f_824_, v___x_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_Internal_List_eraseKey___redArg(v_inst_822_, v_k_823_, v_l_825_);
return v___x_828_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_830_; 
v_val_829_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v___x_827_, 1);
v___x_830_ = l_Std_Internal_List_insertEntry___redArg(v_inst_822_, v_k_823_, v_val_829_, v_l_825_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey(lean_object* v_00_u03b1_831_, lean_object* v_00_u03b2_832_, lean_object* v_inst_833_, lean_object* v_k_834_, lean_object* v_f_835_, lean_object* v_l_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_Internal_List_Const_alterKey___redArg(v_inst_833_, v_k_834_, v_f_835_, v_l_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___redArg(lean_object* v_x_838_, lean_object* v_h__1_839_, lean_object* v_h__2_840_){
_start:
{
if (lean_obj_tag(v_x_838_) == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec(v_h__2_840_);
v___x_841_ = lean_box(0);
v___x_842_ = lean_apply_1(v_h__1_839_, v___x_841_);
return v___x_842_;
}
else
{
lean_object* v_val_843_; lean_object* v___x_844_; 
lean_dec(v_h__1_839_);
v_val_843_ = lean_ctor_get(v_x_838_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v_x_838_, 1);
v___x_844_ = lean_apply_1(v_h__2_840_, v_val_843_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* v_00_u03b2_845_, lean_object* v_motive_846_, lean_object* v_x_847_, lean_object* v_h__1_848_, lean_object* v_h__2_849_){
_start:
{
if (lean_obj_tag(v_x_847_) == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec(v_h__2_849_);
v___x_850_ = lean_box(0);
v___x_851_ = lean_apply_1(v_h__1_848_, v___x_850_);
return v___x_851_;
}
else
{
lean_object* v_val_852_; lean_object* v___x_853_; 
lean_dec(v_h__1_848_);
v_val_852_ = lean_ctor_get(v_x_847_, 0);
lean_inc(v_val_852_);
lean_dec_ref_known(v_x_847_, 1);
v___x_853_ = lean_apply_1(v_h__2_849_, v_val_852_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter___redArg(lean_object* v_x_854_, lean_object* v_h__1_855_, lean_object* v_h__2_856_){
_start:
{
if (lean_obj_tag(v_x_854_) == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v_h__2_856_);
v___x_857_ = lean_box(0);
v___x_858_ = lean_apply_1(v_h__1_855_, v___x_857_);
return v___x_858_;
}
else
{
lean_object* v_val_859_; lean_object* v___x_860_; 
lean_dec(v_h__1_855_);
v_val_859_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v_x_854_, 1);
v___x_860_ = lean_apply_1(v_h__2_856_, v_val_859_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey__cons__perm_match__1_splitter(lean_object* v_00_u03b2_861_, lean_object* v_motive_862_, lean_object* v_x_863_, lean_object* v_h__1_864_, lean_object* v_h__2_865_){
_start:
{
if (lean_obj_tag(v_x_863_) == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v_h__2_865_);
v___x_866_ = lean_box(0);
v___x_867_ = lean_apply_1(v_h__1_864_, v___x_866_);
return v___x_867_;
}
else
{
lean_object* v_val_868_; lean_object* v___x_869_; 
lean_dec(v_h__1_864_);
v_val_868_ = lean_ctor_get(v_x_863_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v_x_863_, 1);
v___x_869_ = lean_apply_1(v_h__2_865_, v_val_868_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey___redArg(lean_object* v_inst_870_, lean_object* v_k_871_, lean_object* v_f_872_, lean_object* v_l_873_){
_start:
{
lean_object* v___x_874_; 
lean_inc(v_l_873_);
lean_inc(v_k_871_);
lean_inc_ref(v_inst_870_);
v___x_874_ = l_Std_Internal_List_getValueCast_x3f___redArg(v_inst_870_, v_k_871_, v_l_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_dec(v_f_872_);
lean_dec(v_k_871_);
lean_dec_ref(v_inst_870_);
return v_l_873_;
}
else
{
lean_object* v_val_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_val_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = lean_apply_1(v_f_872_, v_val_875_);
v___x_877_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_870_, v_k_871_, v___x_876_, v_l_873_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey(lean_object* v_00_u03b1_878_, lean_object* v_00_u03b2_879_, lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_k_882_, lean_object* v_f_883_, lean_object* v_l_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_Internal_List_modifyKey___redArg(v_inst_880_, v_k_882_, v_f_883_, v_l_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey___redArg(lean_object* v_inst_886_, lean_object* v_k_887_, lean_object* v_f_888_, lean_object* v_l_889_){
_start:
{
lean_object* v___x_890_; 
lean_inc(v_l_889_);
lean_inc(v_k_887_);
lean_inc_ref(v_inst_886_);
v___x_890_ = l_Std_Internal_List_getValue_x3f___redArg(v_inst_886_, v_k_887_, v_l_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_dec(v_f_888_);
lean_dec(v_k_887_);
lean_dec_ref(v_inst_886_);
return v_l_889_;
}
else
{
lean_object* v_val_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_val_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = lean_apply_1(v_f_888_, v_val_891_);
v___x_893_ = l_Std_Internal_List_replaceEntry___redArg(v_inst_886_, v_k_887_, v___x_892_, v_l_889_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey(lean_object* v_00_u03b1_894_, lean_object* v_00_u03b2_895_, lean_object* v_inst_896_, lean_object* v_k_897_, lean_object* v_f_898_, lean_object* v_l_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Std_Internal_List_Const_modifyKey___redArg(v_inst_896_, v_k_897_, v_f_898_, v_l_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___redArg(lean_object* v_x_901_, lean_object* v_h__1_902_, lean_object* v_h__2_903_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec(v_h__1_902_);
v___x_904_ = lean_box(0);
v___x_905_ = lean_apply_1(v_h__2_903_, v___x_904_);
return v___x_905_;
}
else
{
lean_object* v_val_906_; lean_object* v___x_907_; 
lean_dec(v_h__2_903_);
v_val_906_ = lean_ctor_get(v_x_901_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v_x_901_, 1);
v___x_907_ = lean_apply_1(v_h__1_902_, v_val_906_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter(lean_object* v_00_u03b1_908_, lean_object* v_motive_909_, lean_object* v_x_910_, lean_object* v_h__1_911_, lean_object* v_h__2_912_){
_start:
{
if (lean_obj_tag(v_x_910_) == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_h__1_911_);
v___x_913_ = lean_box(0);
v___x_914_ = lean_apply_1(v_h__2_912_, v___x_913_);
return v___x_914_;
}
else
{
lean_object* v_val_915_; lean_object* v___x_916_; 
lean_dec(v_h__2_912_);
v_val_915_ = lean_ctor_get(v_x_910_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v_x_910_, 1);
v___x_916_ = lean_apply_1(v_h__1_911_, v_val_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___redArg(lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v_h__1_919_, lean_object* v_h__2_920_){
_start:
{
if (lean_obj_tag(v_x_917_) == 0)
{
lean_object* v___x_921_; 
lean_dec(v_h__2_920_);
v___x_921_ = lean_apply_1(v_h__1_919_, v_x_918_);
return v___x_921_;
}
else
{
lean_object* v_val_922_; lean_object* v___x_923_; 
lean_dec(v_h__1_919_);
v_val_922_ = lean_ctor_get(v_x_917_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v_x_917_, 1);
v___x_923_ = lean_apply_2(v_h__2_920_, v_val_922_, v_x_918_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_motive_926_, lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_h__1_929_, lean_object* v_h__2_930_){
_start:
{
if (lean_obj_tag(v_x_927_) == 0)
{
lean_object* v___x_931_; 
lean_dec(v_h__2_930_);
v___x_931_ = lean_apply_1(v_h__1_929_, v_x_928_);
return v___x_931_;
}
else
{
lean_object* v_val_932_; lean_object* v___x_933_; 
lean_dec(v_h__1_929_);
v_val_932_ = lean_ctor_get(v_x_927_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v_x_927_, 1);
v___x_933_ = lean_apply_2(v_h__2_930_, v_val_932_, v_x_928_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList___redArg(lean_object* v_inst_934_, lean_object* v_l_935_, lean_object* v_toErase_936_){
_start:
{
if (lean_obj_tag(v_toErase_936_) == 0)
{
lean_dec_ref(v_inst_934_);
return v_l_935_;
}
else
{
lean_object* v_head_937_; lean_object* v_tail_938_; lean_object* v___x_939_; 
v_head_937_ = lean_ctor_get(v_toErase_936_, 0);
lean_inc(v_head_937_);
v_tail_938_ = lean_ctor_get(v_toErase_936_, 1);
lean_inc(v_tail_938_);
lean_dec_ref_known(v_toErase_936_, 2);
lean_inc_ref(v_inst_934_);
v___x_939_ = l_Std_Internal_List_eraseKey___redArg(v_inst_934_, v_head_937_, v_l_935_);
v_l_935_ = v___x_939_;
v_toErase_936_ = v_tail_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseList(lean_object* v_00_u03b1_941_, lean_object* v_00_u03b2_942_, lean_object* v_inst_943_, lean_object* v_l_944_, lean_object* v_toErase_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Std_Internal_List_eraseList___redArg(v_inst_943_, v_l_944_, v_toErase_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_947_, lean_object* v_h__1_948_, lean_object* v_h__2_949_){
_start:
{
if (lean_obj_tag(v_opt_947_) == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v_h__1_948_);
v___x_950_ = lean_box(0);
v___x_951_ = lean_apply_1(v_h__2_949_, v___x_950_);
return v___x_951_;
}
else
{
lean_object* v_val_952_; lean_object* v___x_953_; 
lean_dec(v_h__2_949_);
v_val_952_ = lean_ctor_get(v_opt_947_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v_opt_947_, 1);
v___x_953_ = lean_apply_1(v_h__1_948_, v_val_952_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_954_, lean_object* v_motive_955_, lean_object* v_opt_956_, lean_object* v_h__1_957_, lean_object* v_h__2_958_){
_start:
{
if (lean_obj_tag(v_opt_956_) == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v_h__1_957_);
v___x_959_ = lean_box(0);
v___x_960_ = lean_apply_1(v_h__2_958_, v___x_959_);
return v___x_960_;
}
else
{
lean_object* v_val_961_; lean_object* v___x_962_; 
lean_dec(v_h__2_958_);
v_val_961_ = lean_ctor_get(v_opt_956_, 0);
lean_inc(v_val_961_);
lean_dec_ref_known(v_opt_956_, 1);
v___x_962_ = lean_apply_1(v_h__1_957_, v_val_961_);
return v___x_962_;
}
}
}
lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___redArg(){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = lean_box(0);
return v___x_964_;
}
}
LEAN_EXPORT void l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_965_;
v_res_965_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___redArg();
stack->m_obj
 = v_res_965_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___redArg___boxed(lean_object* v___dummy_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___redArg();
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(lean_object* v_00_u03b1_968_, lean_object* v_00_u03b2_969_, lean_object* v_inst_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = lean_box(0);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___boxed(lean_object* v_00_u03b1_972_, lean_object* v_00_u03b2_973_, lean_object* v_inst_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(v_00_u03b1_972_, v_00_u03b2_973_, v_inst_974_);
lean_dec_ref(v_inst_974_);
return v_res_975_;
}
}
uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(lean_object* v_inst_976_, lean_object* v_a_977_, lean_object* v_b_978_){
_start:
{
lean_object* v_fst_979_; lean_object* v_fst_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_fst_979_ = lean_ctor_get(v_a_977_, 0);
lean_inc(v_fst_979_);
lean_dec_ref(v_a_977_);
v_fst_980_ = lean_ctor_get(v_b_978_, 0);
lean_inc(v_fst_980_);
lean_dec_ref(v_b_978_);
v___x_981_ = lean_apply_2(v_inst_976_, v_fst_979_, v_fst_980_);
v___x_982_ = lean_unbox(v___x_981_);
if (v___x_982_ == 2)
{
uint8_t v___x_983_; 
v___x_983_ = 0;
return v___x_983_;
}
else
{
uint8_t v___x_984_; 
v___x_984_ = 1;
return v___x_984_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_976_ = stack[0].m_obj;
lean_object* v_a_977_ = stack[1].m_obj;
lean_object* v_b_978_ = stack[2].m_obj;
uint8_t v_res_985_;
v_res_985_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_976_, v_a_977_, v_b_978_);
stack->m_num = v_res_985_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg___boxed(lean_object* v_inst_986_, lean_object* v_a_987_, lean_object* v_b_988_){
_start:
{
uint8_t v_res_989_; lean_object* v_r_990_; 
v_res_989_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_986_, v_a_987_, v_b_988_);
v_r_990_ = lean_box(v_res_989_);
return v_r_990_;
}
}
uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(lean_object* v_00_u03b1_991_, lean_object* v_00_u03b2_992_, lean_object* v_inst_993_, lean_object* v_a_994_, lean_object* v_b_995_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___redArg(v_inst_993_, v_a_994_, v_b_995_);
return v___x_996_;
}
}
LEAN_EXPORT void l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_993_ = stack[2].m_obj;
lean_object* v_a_994_ = stack[3].m_obj;
lean_object* v_b_995_ = stack[4].m_obj;
uint8_t v_res_997_;
v_res_997_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(lean_box(0), lean_box(0), v_inst_993_, v_a_994_, v_b_995_);
stack->m_num = v_res_997_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___boxed(lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_inst_1000_, lean_object* v_a_1001_, lean_object* v_b_1002_){
_start:
{
uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_res_1003_ = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(v_00_u03b1_998_, v_00_u03b2_999_, v_inst_1000_, v_a_1001_, v_b_1002_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0(lean_object* v_inst_1005_, lean_object* v_a_1006_, lean_object* v_b_1007_){
_start:
{
lean_object* v_fst_1008_; lean_object* v_fst_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v_fst_1008_ = lean_ctor_get(v_a_1006_, 0);
v_fst_1009_ = lean_ctor_get(v_b_1007_, 0);
lean_inc(v_fst_1009_);
lean_inc(v_fst_1008_);
v___x_1010_ = lean_apply_2(v_inst_1005_, v_fst_1008_, v_fst_1009_);
v___x_1011_ = lean_unbox(v___x_1010_);
if (v___x_1011_ == 2)
{
lean_dec_ref(v_a_1006_);
return v_b_1007_;
}
else
{
lean_dec_ref(v_b_1007_);
return v_a_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg(lean_object* v_inst_1012_){
_start:
{
lean_object* v___f_1013_; 
v___f_1013_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1013_, 0, v_inst_1012_);
return v___f_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_inst_1016_){
_start:
{
lean_object* v___f_1017_; 
v___f_1017_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1017_, 0, v_inst_1016_);
return v___f_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___redArg(lean_object* v_inst_1018_, lean_object* v_xs_1019_){
_start:
{
lean_object* v___f_1020_; lean_object* v___x_1021_; 
v___f_1020_ = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1020_, 0, v_inst_1018_);
v___x_1021_ = l_List_min_x3f___redArg(v___f_1020_, v_xs_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f(lean_object* v_00_u03b1_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_inst_1024_, lean_object* v_xs_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_1024_, v_xs_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___redArg(lean_object* v_inst_1027_, lean_object* v_xs_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Std_Internal_List_minEntry_x3f___redArg(v_inst_1027_, v_xs_1028_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_box(0);
return v___x_1030_;
}
else
{
lean_object* v_val_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1039_; 
v_val_1031_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1033_ = v___x_1029_;
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_val_1031_);
lean_dec(v___x_1029_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_fst_1035_; lean_object* v___x_1037_; 
v_fst_1035_ = lean_ctor_get(v_val_1031_, 0);
lean_inc(v_fst_1035_);
lean_dec(v_val_1031_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v_fst_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_fst_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f(lean_object* v_00_u03b1_1040_, lean_object* v_00_u03b2_1041_, lean_object* v_inst_1042_, lean_object* v_xs_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1042_, v_xs_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___redArg(lean_object* v_x_1045_, lean_object* v_h__1_1046_, lean_object* v_h__2_1047_){
_start:
{
if (lean_obj_tag(v_x_1045_) == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec(v_h__2_1047_);
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_apply_1(v_h__1_1046_, v___x_1048_);
return v___x_1049_;
}
else
{
lean_object* v_val_1050_; lean_object* v___x_1051_; 
lean_dec(v_h__1_1046_);
v_val_1050_ = lean_ctor_get(v_x_1045_, 0);
lean_inc(v_val_1050_);
lean_dec_ref_known(v_x_1045_, 1);
v___x_1051_ = lean_apply_1(v_h__2_1047_, v_val_1050_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter(lean_object* v_00_u03b1_1052_, lean_object* v_00_u03b2_1053_, lean_object* v_motive_1054_, lean_object* v_x_1055_, lean_object* v_h__1_1056_, lean_object* v_h__2_1057_){
_start:
{
if (lean_obj_tag(v_x_1055_) == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec(v_h__2_1057_);
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_apply_1(v_h__1_1056_, v___x_1058_);
return v___x_1059_;
}
else
{
lean_object* v_val_1060_; lean_object* v___x_1061_; 
lean_dec(v_h__1_1056_);
v_val_1060_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_val_1060_);
lean_dec_ref_known(v_x_1055_, 1);
v___x_1061_ = lean_apply_1(v_h__2_1057_, v_val_1060_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_1062_, lean_object* v_h__1_1063_, lean_object* v_h__2_1064_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec(v_h__2_1064_);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_apply_1(v_h__1_1063_, v___x_1065_);
return v___x_1066_;
}
else
{
lean_object* v_head_1067_; lean_object* v_tail_1068_; lean_object* v___x_1069_; 
lean_dec(v_h__1_1063_);
v_head_1067_ = lean_ctor_get(v_x_1062_, 0);
lean_inc(v_head_1067_);
v_tail_1068_ = lean_ctor_get(v_x_1062_, 1);
lean_inc(v_tail_1068_);
lean_dec_ref_known(v_x_1062_, 2);
v___x_1069_ = lean_apply_2(v_h__2_1064_, v_head_1067_, v_tail_1068_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_1070_, lean_object* v_motive_1071_, lean_object* v_x_1072_, lean_object* v_h__1_1073_, lean_object* v_h__2_1074_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v_h__2_1074_);
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_apply_1(v_h__1_1073_, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v_head_1077_; lean_object* v_tail_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__1_1073_);
v_head_1077_ = lean_ctor_get(v_x_1072_, 0);
lean_inc(v_head_1077_);
v_tail_1078_ = lean_ctor_get(v_x_1072_, 1);
lean_inc(v_tail_1078_);
lean_dec_ref_known(v_x_1072_, 2);
v___x_1079_ = lean_apply_2(v_h__2_1074_, v_head_1077_, v_tail_1078_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter___redArg(lean_object* v_x_1080_, lean_object* v_h__1_1081_, lean_object* v_h__2_1082_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_h__2_1082_);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_apply_1(v_h__1_1081_, v___x_1083_);
return v___x_1084_;
}
else
{
lean_object* v_val_1085_; lean_object* v___x_1086_; 
lean_dec(v_h__1_1081_);
v_val_1085_ = lean_ctor_get(v_x_1080_, 0);
lean_inc(v_val_1085_);
lean_dec_ref_known(v_x_1080_, 1);
v___x_1086_ = lean_apply_1(v_h__2_1082_, v_val_1085_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__insertEntry_match__1_splitter(lean_object* v_00_u03b1_1087_, lean_object* v_00_u03b2_1088_, lean_object* v_motive_1089_, lean_object* v_x_1090_, lean_object* v_h__1_1091_, lean_object* v_h__2_1092_){
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
lean_object* v_val_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__1_1091_);
v_val_1095_ = lean_ctor_get(v_x_1090_, 0);
lean_inc(v_val_1095_);
lean_dec_ref_known(v_x_1090_, 1);
v___x_1096_ = lean_apply_1(v_h__2_1092_, v_val_1095_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___redArg(lean_object* v_inst_1097_, lean_object* v_xs_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v_val_1100_; 
v___x_1099_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1097_, v_xs_1098_);
v_val_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_val_1100_);
lean_dec(v___x_1099_);
return v_val_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey(lean_object* v_00_u03b1_1101_, lean_object* v_00_u03b2_1102_, lean_object* v_inst_1103_, lean_object* v_xs_1104_, lean_object* v_h_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Std_Internal_List_minKey___redArg(v_inst_1103_, v_xs_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___redArg(lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_xs_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1107_, v_xs_1109_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_1112_ = l_panic___redArg(v_inst_1108_, v___x_1111_);
return v___x_1112_;
}
else
{
lean_object* v_val_1113_; 
v_val_1113_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v___x_1110_, 1);
return v_val_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___redArg___boxed(lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_xs_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_1114_, v_inst_1115_, v_xs_1116_);
lean_dec(v_inst_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21(lean_object* v_00_u03b1_1118_, lean_object* v_00_u03b2_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_xs_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Std_Internal_List_minKey_x21___redArg(v_inst_1120_, v_inst_1121_, v_xs_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___boxed(lean_object* v_00_u03b1_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_xs_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Std_Internal_List_minKey_x21(v_00_u03b1_1124_, v_00_u03b2_1125_, v_inst_1126_, v_inst_1127_, v_xs_1128_);
lean_dec(v_inst_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg(lean_object* v_inst_1130_, lean_object* v_xs_1131_, lean_object* v_fallback_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Std_Internal_List_minKey_x3f___redArg(v_inst_1130_, v_xs_1131_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_inc(v_fallback_1132_);
return v_fallback_1132_;
}
else
{
lean_object* v_val_1134_; 
v_val_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_val_1134_);
lean_dec_ref_known(v___x_1133_, 1);
return v_val_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___redArg___boxed(lean_object* v_inst_1135_, lean_object* v_xs_1136_, lean_object* v_fallback_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Std_Internal_List_minKeyD___redArg(v_inst_1135_, v_xs_1136_, v_fallback_1137_);
lean_dec(v_fallback_1137_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD(lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_inst_1141_, lean_object* v_xs_1142_, lean_object* v_fallback_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_Internal_List_minKeyD___redArg(v_inst_1141_, v_xs_1142_, v_fallback_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___boxed(lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_inst_1147_, lean_object* v_xs_1148_, lean_object* v_fallback_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_Internal_List_minKeyD(v_00_u03b1_1145_, v_00_u03b2_1146_, v_inst_1147_, v_xs_1148_, v_fallback_1149_);
lean_dec(v_fallback_1149_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f___redArg(lean_object* v_inst_1151_, lean_object* v_xs_1152_){
_start:
{
lean_object* v___f_1153_; lean_object* v___x_1154_; 
v___f_1153_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1153_, 0, v_inst_1151_);
v___x_1154_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1153_, v_xs_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f(lean_object* v_00_u03b1_1155_, lean_object* v_00_u03b2_1156_, lean_object* v_inst_1157_, lean_object* v_xs_1158_){
_start:
{
lean_object* v___f_1159_; lean_object* v___x_1160_; 
v___f_1159_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1159_, 0, v_inst_1157_);
v___x_1160_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1159_, v_xs_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey___redArg(lean_object* v_inst_1161_, lean_object* v_xs_1162_){
_start:
{
lean_object* v___f_1163_; lean_object* v___x_1164_; 
v___f_1163_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1163_, 0, v_inst_1161_);
v___x_1164_ = l_Std_Internal_List_minKey___redArg(v___f_1163_, v_xs_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey(lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_inst_1167_, lean_object* v_xs_1168_, lean_object* v_h_1169_){
_start:
{
lean_object* v___f_1170_; lean_object* v___x_1171_; 
v___f_1170_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1170_, 0, v_inst_1167_);
v___x_1171_ = l_Std_Internal_List_minKey___redArg(v___f_1170_, v_xs_1168_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg(lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_xs_1174_){
_start:
{
lean_object* v___f_1175_; lean_object* v___x_1176_; 
v___f_1175_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1175_, 0, v_inst_1172_);
v___x_1176_ = l_Std_Internal_List_minKey_x3f___redArg(v___f_1175_, v_xs_1174_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_obj_once(&l_Std_Internal_List_getValueCast_x21___redArg___closed__3, &l_Std_Internal_List_getValueCast_x21___redArg___closed__3_once, _init_l_Std_Internal_List_getValueCast_x21___redArg___closed__3);
v___x_1178_ = l_panic___redArg(v_inst_1173_, v___x_1177_);
return v___x_1178_;
}
else
{
lean_object* v_val_1179_; 
v_val_1179_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_val_1179_);
lean_dec_ref_known(v___x_1176_, 1);
return v_val_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___redArg___boxed(lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_xs_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_1180_, v_inst_1181_, v_xs_1182_);
lean_dec(v_inst_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21(lean_object* v_00_u03b1_1184_, lean_object* v_00_u03b2_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_xs_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Std_Internal_List_maxKey_x21___redArg(v_inst_1186_, v_inst_1187_, v_xs_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_00_u03b2_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_xs_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Std_Internal_List_maxKey_x21(v_00_u03b1_1190_, v_00_u03b2_1191_, v_inst_1192_, v_inst_1193_, v_xs_1194_);
lean_dec(v_inst_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg(lean_object* v_inst_1196_, lean_object* v_xs_1197_, lean_object* v_fallback_1198_){
_start:
{
lean_object* v___f_1199_; lean_object* v___x_1200_; 
v___f_1199_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1199_, 0, v_inst_1196_);
v___x_1200_ = l_Std_Internal_List_minKeyD___redArg(v___f_1199_, v_xs_1197_, v_fallback_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___redArg___boxed(lean_object* v_inst_1201_, lean_object* v_xs_1202_, lean_object* v_fallback_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Std_Internal_List_maxKeyD___redArg(v_inst_1201_, v_xs_1202_, v_fallback_1203_);
lean_dec(v_fallback_1203_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD(lean_object* v_00_u03b1_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_inst_1207_, lean_object* v_xs_1208_, lean_object* v_fallback_1209_){
_start:
{
lean_object* v___f_1210_; lean_object* v___x_1211_; 
v___f_1210_ = lean_alloc_closure((void*)(l_Ord_opposite___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1210_, 0, v_inst_1207_);
v___x_1211_ = l_Std_Internal_List_minKeyD___redArg(v___f_1210_, v_xs_1208_, v_fallback_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___boxed(lean_object* v_00_u03b1_1212_, lean_object* v_00_u03b2_1213_, lean_object* v_inst_1214_, lean_object* v_xs_1215_, lean_object* v_fallback_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_Internal_List_maxKeyD(v_00_u03b1_1212_, v_00_u03b2_1213_, v_inst_1214_, v_xs_1215_, v_fallback_1216_);
lean_dec(v_fallback_1216_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn___redArg(lean_object* v_inst_1218_, lean_object* v_l_1219_, lean_object* v_sofar_1220_, lean_object* v_k_1221_){
_start:
{
lean_object* v___x_1222_; 
lean_inc_ref(v_inst_1218_);
v___x_1222_ = l_Std_Internal_List_getEntry_x3f___redArg(v_inst_1218_, v_k_1221_, v_l_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_dec_ref(v_inst_1218_);
return v_sofar_1220_;
}
else
{
lean_object* v_val_1223_; lean_object* v_fst_1224_; lean_object* v_snd_1225_; lean_object* v___x_1226_; 
v_val_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_val_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v_fst_1224_ = lean_ctor_get(v_val_1223_, 0);
lean_inc(v_fst_1224_);
v_snd_1225_ = lean_ctor_get(v_val_1223_, 1);
lean_inc(v_snd_1225_);
lean_dec(v_val_1223_);
v___x_1226_ = l_Std_Internal_List_insertEntry___redArg(v_inst_1218_, v_fst_1224_, v_snd_1225_, v_sofar_1220_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmallerFn(lean_object* v_00_u03b1_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_inst_1229_, lean_object* v_l_1230_, lean_object* v_sofar_1231_, lean_object* v_k_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Std_Internal_List_interSmallerFn___redArg(v_inst_1229_, v_l_1230_, v_sofar_1231_, v_k_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_1234_, lean_object* v_h__1_1235_, lean_object* v_h__2_1236_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_h__1_1235_);
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_apply_1(v_h__2_1236_, v___x_1237_);
return v___x_1238_;
}
else
{
lean_object* v_val_1239_; lean_object* v___x_1240_; 
lean_dec(v_h__2_1236_);
v_val_1239_ = lean_ctor_get(v_x_1234_, 0);
lean_inc(v_val_1239_);
lean_dec_ref_known(v_x_1234_, 1);
v___x_1240_ = lean_apply_1(v_h__1_1235_, v_val_1239_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_1241_, lean_object* v_00_u03b2_1242_, lean_object* v_motive_1243_, lean_object* v_x_1244_, lean_object* v_h__1_1245_, lean_object* v_h__2_1246_){
_start:
{
if (lean_obj_tag(v_x_1244_) == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec(v_h__1_1245_);
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_apply_1(v_h__2_1246_, v___x_1247_);
return v___x_1248_;
}
else
{
lean_object* v_val_1249_; lean_object* v___x_1250_; 
lean_dec(v_h__2_1246_);
v_val_1249_ = lean_ctor_get(v_x_1244_, 0);
lean_inc(v_val_1249_);
lean_dec_ref_known(v_x_1244_, 1);
v___x_1250_ = lean_apply_1(v_h__1_1245_, v_val_1249_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg___lam__0(lean_object* v_inst_1251_, lean_object* v_l_u2081_1252_, lean_object* v_sofar_1253_, lean_object* v_kv_1254_){
_start:
{
lean_object* v_fst_1255_; lean_object* v___x_1256_; 
v_fst_1255_ = lean_ctor_get(v_kv_1254_, 0);
lean_inc(v_fst_1255_);
lean_dec_ref(v_kv_1254_);
v___x_1256_ = l_Std_Internal_List_interSmallerFn___redArg(v_inst_1251_, v_l_u2081_1252_, v_sofar_1253_, v_fst_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller___redArg(lean_object* v_inst_1257_, lean_object* v_l_u2081_1258_, lean_object* v_l_u2082_1259_){
_start:
{
lean_object* v___f_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___f_1260_ = lean_alloc_closure((void*)(l_Std_Internal_List_interSmaller___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1260_, 0, v_inst_1257_);
lean_closure_set(v___f_1260_, 1, v_l_u2081_1258_);
v___x_1261_ = lean_box(0);
v___x_1262_ = l_List_foldl___redArg(v___f_1260_, v___x_1261_, v_l_u2082_1259_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_interSmaller(lean_object* v_00_u03b1_1263_, lean_object* v_00_u03b2_1264_, lean_object* v_inst_1265_, lean_object* v_l_u2081_1266_, lean_object* v_l_u2082_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_Internal_List_interSmaller___redArg(v_inst_1265_, v_l_u2081_1266_, v_l_u2082_1267_);
return v___x_1268_;
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
