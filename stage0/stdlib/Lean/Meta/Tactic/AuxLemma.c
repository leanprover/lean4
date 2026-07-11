// Lean compiler output
// Module: Lean.Meta.Tactic.AuxLemma
// Imports: public import Lean.AddDecl public import Lean.DefEqAttrib
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
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_defeqAttr;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqAuxLemmaKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqAuxLemmaKey_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqAuxLemmaKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqAuxLemmaKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqAuxLemmaKey___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqAuxLemmaKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqAuxLemmaKey = (const lean_object*)&l_Lean_Meta_instBEqAuxLemmaKey___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_instHashableAuxLemmaKey_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableAuxLemmaKey_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_instHashableAuxLemmaKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instHashableAuxLemmaKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instHashableAuxLemmaKey___closed__0 = (const lean_object*)&l_Lean_Meta_instHashableAuxLemmaKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instHashableAuxLemmaKey = (const lean_object*)&l_Lean_Meta_instHashableAuxLemmaKey___closed__0_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedAuxLemmas_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedAuxLemmas;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_auxLemmasExt;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0;
static lean_once_cell_t l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1;
static lean_once_cell_t l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2;
static lean_once_cell_t l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkAuxLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_proof"};
static const lean_object* l_Lean_Meta_mkAuxLemma___closed__0 = (const lean_object*)&l_Lean_Meta_mkAuxLemma___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkAuxLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkAuxLemma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 32, 192, 173, 72, 22, 234, 250)}};
static const lean_object* l_Lean_Meta_mkAuxLemma___closed__1 = (const lean_object*)&l_Lean_Meta_mkAuxLemma___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqAuxLemmaKey_beq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_type_3_; uint8_t v_isPrivate_4_; uint8_t v_defeq_5_; lean_object* v_type_6_; uint8_t v_isPrivate_7_; uint8_t v_defeq_8_; uint8_t v___y_10_; uint8_t v___x_11_; 
v_type_3_ = lean_ctor_get(v_x_1_, 0);
v_isPrivate_4_ = lean_ctor_get_uint8(v_x_1_, sizeof(void*)*1);
v_defeq_5_ = lean_ctor_get_uint8(v_x_1_, sizeof(void*)*1 + 1);
v_type_6_ = lean_ctor_get(v_x_2_, 0);
v_isPrivate_7_ = lean_ctor_get_uint8(v_x_2_, sizeof(void*)*1);
v_defeq_8_ = lean_ctor_get_uint8(v_x_2_, sizeof(void*)*1 + 1);
v___x_11_ = lean_expr_eqv(v_type_3_, v_type_6_);
if (v___x_11_ == 0)
{
return v___x_11_;
}
else
{
if (v_isPrivate_4_ == 0)
{
if (v_isPrivate_7_ == 0)
{
v___y_10_ = v___x_11_;
goto v___jp_9_;
}
else
{
return v_isPrivate_4_;
}
}
else
{
v___y_10_ = v_isPrivate_7_;
goto v___jp_9_;
}
}
v___jp_9_:
{
if (v___y_10_ == 0)
{
return v___y_10_;
}
else
{
if (v_defeq_5_ == 0)
{
if (v_defeq_8_ == 0)
{
return v___y_10_;
}
else
{
return v_defeq_5_;
}
}
else
{
return v_defeq_8_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqAuxLemmaKey_beq___boxed(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_12_, v_x_13_);
lean_dec_ref(v_x_13_);
lean_dec_ref(v_x_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_instHashableAuxLemmaKey_hash(lean_object* v_x_18_){
_start:
{
lean_object* v_type_19_; uint8_t v_isPrivate_20_; uint8_t v_defeq_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v___y_26_; 
v_type_19_ = lean_ctor_get(v_x_18_, 0);
v_isPrivate_20_ = lean_ctor_get_uint8(v_x_18_, sizeof(void*)*1);
v_defeq_21_ = lean_ctor_get_uint8(v_x_18_, sizeof(void*)*1 + 1);
v___x_22_ = 0ULL;
v___x_23_ = l_Lean_Expr_hash(v_type_19_);
v___x_24_ = lean_uint64_mix_hash(v___x_22_, v___x_23_);
if (v_isPrivate_20_ == 0)
{
uint64_t v___x_32_; 
v___x_32_ = 13ULL;
v___y_26_ = v___x_32_;
goto v___jp_25_;
}
else
{
uint64_t v___x_33_; 
v___x_33_ = 11ULL;
v___y_26_ = v___x_33_;
goto v___jp_25_;
}
v___jp_25_:
{
uint64_t v___x_27_; 
v___x_27_ = lean_uint64_mix_hash(v___x_24_, v___y_26_);
if (v_defeq_21_ == 0)
{
uint64_t v___x_28_; uint64_t v___x_29_; 
v___x_28_ = 13ULL;
v___x_29_ = lean_uint64_mix_hash(v___x_27_, v___x_28_);
return v___x_29_;
}
else
{
uint64_t v___x_30_; uint64_t v___x_31_; 
v___x_30_ = 11ULL;
v___x_31_ = lean_uint64_mix_hash(v___x_27_, v___x_30_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableAuxLemmaKey_hash___boxed(lean_object* v_x_34_){
_start:
{
uint64_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_34_);
lean_dec_ref(v_x_34_);
v_r_36_ = lean_box_uint64(v_res_35_);
return v_r_36_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas_default(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(lean_object* v___x_44_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object* v___x_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(v___x_47_);
return v_res_49_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_50_; lean_object* v___f_51_; 
v___x_50_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1);
v___f_51_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_51_, 0, v___x_50_);
return v___f_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___f_53_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_box(1);
v___x_56_ = l_Lean_registerEnvExtension___redArg(v___f_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(lean_object* v_kind_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_auxDeclNGen_63_; lean_object* v___x_64_; lean_object* v_env_65_; lean_object* v___x_66_; lean_object* v_fst_67_; lean_object* v_snd_68_; lean_object* v___x_69_; lean_object* v_env_70_; lean_object* v_nextMacroScope_71_; lean_object* v_ngen_72_; lean_object* v_traceState_73_; lean_object* v_cache_74_; lean_object* v_messages_75_; lean_object* v_infoState_76_; lean_object* v_snapshotTasks_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_86_; 
v___x_62_ = lean_st_ref_get(v___y_60_);
v_auxDeclNGen_63_ = lean_ctor_get(v___x_62_, 3);
lean_inc_ref(v_auxDeclNGen_63_);
lean_dec(v___x_62_);
v___x_64_ = lean_st_ref_get(v___y_60_);
v_env_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_env_65_);
lean_dec(v___x_64_);
v___x_66_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_65_, v_auxDeclNGen_63_, v_kind_59_);
v_fst_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_fst_67_);
v_snd_68_ = lean_ctor_get(v___x_66_, 1);
lean_inc(v_snd_68_);
lean_dec_ref(v___x_66_);
v___x_69_ = lean_st_ref_take(v___y_60_);
v_env_70_ = lean_ctor_get(v___x_69_, 0);
v_nextMacroScope_71_ = lean_ctor_get(v___x_69_, 1);
v_ngen_72_ = lean_ctor_get(v___x_69_, 2);
v_traceState_73_ = lean_ctor_get(v___x_69_, 4);
v_cache_74_ = lean_ctor_get(v___x_69_, 5);
v_messages_75_ = lean_ctor_get(v___x_69_, 6);
v_infoState_76_ = lean_ctor_get(v___x_69_, 7);
v_snapshotTasks_77_ = lean_ctor_get(v___x_69_, 8);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_86_ == 0)
{
lean_object* v_unused_87_; 
v_unused_87_ = lean_ctor_get(v___x_69_, 3);
lean_dec(v_unused_87_);
v___x_79_ = v___x_69_;
v_isShared_80_ = v_isSharedCheck_86_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_snapshotTasks_77_);
lean_inc(v_infoState_76_);
lean_inc(v_messages_75_);
lean_inc(v_cache_74_);
lean_inc(v_traceState_73_);
lean_inc(v_ngen_72_);
lean_inc(v_nextMacroScope_71_);
lean_inc(v_env_70_);
lean_dec(v___x_69_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_86_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 3, v_snd_68_);
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_env_70_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_nextMacroScope_71_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v_ngen_72_);
lean_ctor_set(v_reuseFailAlloc_85_, 3, v_snd_68_);
lean_ctor_set(v_reuseFailAlloc_85_, 4, v_traceState_73_);
lean_ctor_set(v_reuseFailAlloc_85_, 5, v_cache_74_);
lean_ctor_set(v_reuseFailAlloc_85_, 6, v_messages_75_);
lean_ctor_set(v_reuseFailAlloc_85_, 7, v_infoState_76_);
lean_ctor_set(v_reuseFailAlloc_85_, 8, v_snapshotTasks_77_);
v___x_82_ = v_reuseFailAlloc_85_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_st_ref_set(v___y_60_, v___x_82_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v_fst_67_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg___boxed(lean_object* v_kind_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_88_, v___y_89_);
lean_dec(v___y_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(lean_object* v_kind_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_92_, v___y_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___boxed(lean_object* v_kind_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(v_kind_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(lean_object* v_x_106_, lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
lean_object* v_ks_110_; lean_object* v_vs_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_135_; 
v_ks_110_ = lean_ctor_get(v_x_106_, 0);
v_vs_111_ = lean_ctor_get(v_x_106_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_x_106_);
if (v_isSharedCheck_135_ == 0)
{
v___x_113_ = v_x_106_;
v_isShared_114_ = v_isSharedCheck_135_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_vs_111_);
lean_inc(v_ks_110_);
lean_dec(v_x_106_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_135_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = lean_array_get_size(v_ks_110_);
v___x_116_ = lean_nat_dec_lt(v_x_107_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
lean_dec(v_x_107_);
v___x_117_ = lean_array_push(v_ks_110_, v_x_108_);
v___x_118_ = lean_array_push(v_vs_111_, v_x_109_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_118_);
lean_ctor_set(v___x_113_, 0, v___x_117_);
v___x_120_ = v___x_113_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
else
{
lean_object* v_k_x27_122_; uint8_t v___x_123_; 
v_k_x27_122_ = lean_array_fget_borrowed(v_ks_110_, v_x_107_);
v___x_123_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_108_, v_k_x27_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_125_; 
if (v_isShared_114_ == 0)
{
v___x_125_ = v___x_113_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_ks_110_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_vs_111_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_add(v_x_107_, v___x_126_);
lean_dec(v_x_107_);
v_x_106_ = v___x_125_;
v_x_107_ = v___x_127_;
goto _start;
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_130_ = lean_array_fset(v_ks_110_, v_x_107_, v_x_108_);
v___x_131_ = lean_array_fset(v_vs_111_, v_x_107_, v_x_109_);
lean_dec(v_x_107_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_131_);
lean_ctor_set(v___x_113_, 0, v___x_130_);
v___x_133_ = v___x_113_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(lean_object* v_n_136_, lean_object* v_k_137_, lean_object* v_v_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_n_136_, v___x_139_, v_k_137_, v_v_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object* v_x_142_, size_t v_x_143_, size_t v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v_es_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v_j_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_es_147_ = lean_ctor_get(v_x_142_, 0);
v___x_148_ = ((size_t)31ULL);
v___x_149_ = lean_usize_land(v_x_143_, v___x_148_);
v_j_150_ = lean_usize_to_nat(v___x_149_);
v___x_151_ = lean_array_get_size(v_es_147_);
v___x_152_ = lean_nat_dec_lt(v_j_150_, v___x_151_);
if (v___x_152_ == 0)
{
lean_dec(v_j_150_);
lean_dec(v_x_146_);
lean_dec_ref(v_x_145_);
return v_x_142_;
}
else
{
lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_191_; 
lean_inc_ref(v_es_147_);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v_x_142_, 0);
lean_dec(v_unused_192_);
v___x_154_ = v_x_142_;
v_isShared_155_ = v_isSharedCheck_191_;
goto v_resetjp_153_;
}
else
{
lean_dec(v_x_142_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_191_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v_v_156_; lean_object* v___x_157_; lean_object* v_xs_x27_158_; lean_object* v___y_160_; 
v_v_156_ = lean_array_fget(v_es_147_, v_j_150_);
v___x_157_ = lean_box(0);
v_xs_x27_158_ = lean_array_fset(v_es_147_, v_j_150_, v___x_157_);
switch(lean_obj_tag(v_v_156_))
{
case 0:
{
lean_object* v_key_165_; lean_object* v_val_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_176_; 
v_key_165_ = lean_ctor_get(v_v_156_, 0);
v_val_166_ = lean_ctor_get(v_v_156_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_v_156_);
if (v_isSharedCheck_176_ == 0)
{
v___x_168_ = v_v_156_;
v_isShared_169_ = v_isSharedCheck_176_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_val_166_);
lean_inc(v_key_165_);
lean_dec(v_v_156_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_176_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
uint8_t v___x_170_; 
v___x_170_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_145_, v_key_165_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_del_object(v___x_168_);
v___x_171_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_165_, v_val_166_, v_x_145_, v_x_146_);
v___x_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
v___y_160_ = v___x_172_;
goto v___jp_159_;
}
else
{
lean_object* v___x_174_; 
lean_dec(v_val_166_);
lean_dec(v_key_165_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v_x_146_);
lean_ctor_set(v___x_168_, 0, v_x_145_);
v___x_174_ = v___x_168_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_x_145_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_x_146_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
v___y_160_ = v___x_174_;
goto v___jp_159_;
}
}
}
}
case 1:
{
lean_object* v_node_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_189_; 
v_node_177_ = lean_ctor_get(v_v_156_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v_v_156_);
if (v_isSharedCheck_189_ == 0)
{
v___x_179_ = v_v_156_;
v_isShared_180_ = v_isSharedCheck_189_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_node_177_);
lean_dec(v_v_156_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_189_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
size_t v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_181_ = ((size_t)5ULL);
v___x_182_ = lean_usize_shift_right(v_x_143_, v___x_181_);
v___x_183_ = ((size_t)1ULL);
v___x_184_ = lean_usize_add(v_x_144_, v___x_183_);
v___x_185_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_node_177_, v___x_182_, v___x_184_, v_x_145_, v_x_146_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_185_);
v___x_187_ = v___x_179_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
v___y_160_ = v___x_187_;
goto v___jp_159_;
}
}
}
default: 
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_x_145_);
lean_ctor_set(v___x_190_, 1, v_x_146_);
v___y_160_ = v___x_190_;
goto v___jp_159_;
}
}
v___jp_159_:
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = lean_array_fset(v_xs_x27_158_, v_j_150_, v___y_160_);
lean_dec(v_j_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_161_);
v___x_163_ = v___x_154_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
else
{
lean_object* v_ks_193_; lean_object* v_vs_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_214_; 
v_ks_193_ = lean_ctor_get(v_x_142_, 0);
v_vs_194_ = lean_ctor_get(v_x_142_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_214_ == 0)
{
v___x_196_ = v_x_142_;
v_isShared_197_ = v_isSharedCheck_214_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_vs_194_);
lean_inc(v_ks_193_);
lean_dec(v_x_142_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_214_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_ks_193_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_vs_194_);
v___x_199_ = v_reuseFailAlloc_213_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v_newNode_200_; uint8_t v___y_202_; size_t v___x_208_; uint8_t v___x_209_; 
v_newNode_200_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v___x_199_, v_x_145_, v_x_146_);
v___x_208_ = ((size_t)7ULL);
v___x_209_ = lean_usize_dec_le(v___x_208_, v_x_144_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_210_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_200_);
v___x_211_ = lean_unsigned_to_nat(4u);
v___x_212_ = lean_nat_dec_lt(v___x_210_, v___x_211_);
lean_dec(v___x_210_);
v___y_202_ = v___x_212_;
goto v___jp_201_;
}
else
{
v___y_202_ = v___x_209_;
goto v___jp_201_;
}
v___jp_201_:
{
if (v___y_202_ == 0)
{
lean_object* v_ks_203_; lean_object* v_vs_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_ks_203_ = lean_ctor_get(v_newNode_200_, 0);
lean_inc_ref(v_ks_203_);
v_vs_204_ = lean_ctor_get(v_newNode_200_, 1);
lean_inc_ref(v_vs_204_);
lean_dec_ref(v_newNode_200_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0);
v___x_207_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_x_144_, v_ks_203_, v_vs_204_, v___x_205_, v___x_206_);
lean_dec_ref(v_vs_204_);
lean_dec_ref(v_ks_203_);
return v___x_207_;
}
else
{
return v_newNode_200_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t v_depth_215_, lean_object* v_keys_216_, lean_object* v_vals_217_, lean_object* v_i_218_, lean_object* v_entries_219_){
_start:
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = lean_array_get_size(v_keys_216_);
v___x_221_ = lean_nat_dec_lt(v_i_218_, v___x_220_);
if (v___x_221_ == 0)
{
lean_dec(v_i_218_);
return v_entries_219_;
}
else
{
lean_object* v_k_222_; lean_object* v_v_223_; uint64_t v___x_224_; size_t v_h_225_; size_t v___x_226_; lean_object* v___x_227_; size_t v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v_h_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_k_222_ = lean_array_fget_borrowed(v_keys_216_, v_i_218_);
v_v_223_ = lean_array_fget_borrowed(v_vals_217_, v_i_218_);
v___x_224_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_k_222_);
v_h_225_ = lean_uint64_to_usize(v___x_224_);
v___x_226_ = ((size_t)5ULL);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_sub(v_depth_215_, v___x_228_);
v___x_230_ = lean_usize_mul(v___x_226_, v___x_229_);
v_h_231_ = lean_usize_shift_right(v_h_225_, v___x_230_);
v___x_232_ = lean_nat_add(v_i_218_, v___x_227_);
lean_dec(v_i_218_);
lean_inc(v_v_223_);
lean_inc(v_k_222_);
v___x_233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_entries_219_, v_h_231_, v_depth_215_, v_k_222_, v_v_223_);
v_i_218_ = v___x_232_;
v_entries_219_ = v___x_233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_235_, lean_object* v_keys_236_, lean_object* v_vals_237_, lean_object* v_i_238_, lean_object* v_entries_239_){
_start:
{
size_t v_depth_boxed_240_; lean_object* v_res_241_; 
v_depth_boxed_240_ = lean_unbox_usize(v_depth_235_);
lean_dec(v_depth_235_);
v_res_241_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_boxed_240_, v_keys_236_, v_vals_237_, v_i_238_, v_entries_239_);
lean_dec_ref(v_vals_237_);
lean_dec_ref(v_keys_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
size_t v_x_6150__boxed_247_; size_t v_x_6151__boxed_248_; lean_object* v_res_249_; 
v_x_6150__boxed_247_ = lean_unbox_usize(v_x_243_);
lean_dec(v_x_243_);
v_x_6151__boxed_248_ = lean_unbox_usize(v_x_244_);
lean_dec(v_x_244_);
v_res_249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_242_, v_x_6150__boxed_247_, v_x_6151__boxed_248_, v_x_245_, v_x_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
uint64_t v___x_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; 
v___x_253_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_251_);
v___x_254_ = lean_uint64_to_usize(v___x_253_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_250_, v___x_254_, v___x_255_, v_x_251_, v_x_252_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object* v_a_257_, lean_object* v_levelParams_258_, lean_object* v___x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_a_257_);
lean_ctor_set(v___x_261_, 1, v_levelParams_258_);
v___x_262_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_260_, v___x_259_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(lean_object* v_msgData_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; lean_object* v_env_270_; lean_object* v___x_271_; lean_object* v_mctx_272_; lean_object* v_lctx_273_; lean_object* v_options_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_269_ = lean_st_ref_get(v___y_267_);
v_env_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc_ref(v_env_270_);
lean_dec(v___x_269_);
v___x_271_ = lean_st_ref_get(v___y_265_);
v_mctx_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_mctx_272_);
lean_dec(v___x_271_);
v_lctx_273_ = lean_ctor_get(v___y_264_, 2);
v_options_274_ = lean_ctor_get(v___y_266_, 2);
lean_inc_ref(v_options_274_);
lean_inc_ref(v_lctx_273_);
v___x_275_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_275_, 0, v_env_270_);
lean_ctor_set(v___x_275_, 1, v_mctx_272_);
lean_ctor_set(v___x_275_, 2, v_lctx_273_);
lean_ctor_set(v___x_275_, 3, v_options_274_);
v___x_276_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v_msgData_263_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_msgData_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msgData_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_ref_291_; lean_object* v___x_292_; lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
v_ref_291_ = lean_ctor_get(v___y_288_, 5);
v___x_292_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msg_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_301_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
lean_inc(v_ref_291_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_ref_291_);
lean_ctor_set(v___x_297_, 1, v_a_293_);
if (v_isShared_296_ == 0)
{
lean_ctor_set_tag(v___x_295_, 1);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_308_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0));
v___x_311_ = l_Lean_stringToMessageData(v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2));
v___x_314_ = l_Lean_stringToMessageData(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4));
v___x_317_ = l_Lean_stringToMessageData(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6));
v___x_320_ = l_Lean_stringToMessageData(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8));
v___x_323_ = l_Lean_stringToMessageData(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(lean_object* v_attrName_324_, lean_object* v_declName_325_, lean_object* v_asyncPrefix_x3f_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v___y_333_; 
if (lean_obj_tag(v_asyncPrefix_x3f_326_) == 0)
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_MessageData_nil;
v___y_333_ = v___x_346_;
goto v___jp_332_;
}
else
{
lean_object* v_val_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_val_347_ = lean_ctor_get(v_asyncPrefix_x3f_326_, 0);
lean_inc(v_val_347_);
lean_dec_ref_known(v_asyncPrefix_x3f_326_, 1);
v___x_348_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7);
v___x_349_ = l_Lean_MessageData_ofName(v_val_347_);
v___x_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9);
v___x_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___y_333_ = v___x_352_;
goto v___jp_332_;
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_334_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_335_ = l_Lean_MessageData_ofName(v_attrName_324_);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = 0;
v___x_340_ = l_Lean_MessageData_ofConstName(v_declName_325_, v___x_339_);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_338_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___y_333_);
v___x_345_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_344_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object* v_attrName_353_, lean_object* v_declName_354_, lean_object* v_asyncPrefix_x3f_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_353_, v_declName_354_, v_asyncPrefix_x3f_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_361_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(lean_object* v_attrName_365_, lean_object* v_declName_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_372_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_373_ = l_Lean_MessageData_ofName(v_attrName_365_);
v___x_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = 0;
v___x_378_ = l_Lean_MessageData_ofConstName(v_declName_366_, v___x_377_);
v___x_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_376_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1);
v___x_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_381_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___boxed(lean_object* v_attrName_383_, lean_object* v_declName_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_383_, v_declName_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_390_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_391_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_397_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
lean_ctor_set(v___x_397_, 2, v___x_396_);
lean_ctor_set(v___x_397_, 3, v___x_396_);
lean_ctor_set(v___x_397_, 4, v___x_396_);
lean_ctor_set(v___x_397_, 5, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object* v_attr_398_, lean_object* v_decl_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___x_448_; lean_object* v_env_449_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___x_464_; 
v___x_448_ = lean_st_ref_get(v___y_403_);
v_env_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_env_449_);
lean_dec(v___x_448_);
v___x_464_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_449_, v_decl_399_);
if (lean_obj_tag(v___x_464_) == 0)
{
v___y_451_ = v___y_400_;
v___y_452_ = v___y_401_;
v___y_453_ = v___y_402_;
v___y_454_ = v___y_403_;
goto v___jp_450_;
}
else
{
lean_object* v_attr_465_; lean_object* v_toAttributeImplCore_466_; lean_object* v_name_467_; lean_object* v___x_468_; 
lean_dec_ref_known(v___x_464_, 1);
lean_dec_ref(v_env_449_);
v_attr_465_ = lean_ctor_get(v_attr_398_, 0);
lean_inc_ref(v_attr_465_);
lean_dec_ref(v_attr_398_);
v_toAttributeImplCore_466_ = lean_ctor_get(v_attr_465_, 0);
lean_inc_ref(v_toAttributeImplCore_466_);
lean_dec_ref(v_attr_465_);
v_name_467_ = lean_ctor_get(v_toAttributeImplCore_466_, 1);
lean_inc(v_name_467_);
lean_dec_ref(v_toAttributeImplCore_466_);
v___x_468_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_name_467_, v_decl_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
return v___x_468_;
}
v___jp_405_:
{
lean_object* v___x_408_; lean_object* v_ext_409_; lean_object* v_toEnvExtension_410_; lean_object* v_env_411_; lean_object* v_nextMacroScope_412_; lean_object* v_ngen_413_; lean_object* v_auxDeclNGen_414_; lean_object* v_traceState_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_446_; 
v___x_408_ = lean_st_ref_take(v___y_407_);
v_ext_409_ = lean_ctor_get(v_attr_398_, 1);
lean_inc_ref(v_ext_409_);
lean_dec_ref(v_attr_398_);
v_toEnvExtension_410_ = lean_ctor_get(v_ext_409_, 0);
v_env_411_ = lean_ctor_get(v___x_408_, 0);
v_nextMacroScope_412_ = lean_ctor_get(v___x_408_, 1);
v_ngen_413_ = lean_ctor_get(v___x_408_, 2);
v_auxDeclNGen_414_ = lean_ctor_get(v___x_408_, 3);
v_traceState_415_ = lean_ctor_get(v___x_408_, 4);
v_messages_416_ = lean_ctor_get(v___x_408_, 6);
v_infoState_417_ = lean_ctor_get(v___x_408_, 7);
v_snapshotTasks_418_ = lean_ctor_get(v___x_408_, 8);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v___x_408_, 5);
lean_dec(v_unused_447_);
v___x_420_ = v___x_408_;
v_isShared_421_ = v_isSharedCheck_446_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_traceState_415_);
lean_inc(v_auxDeclNGen_414_);
lean_inc(v_ngen_413_);
lean_inc(v_nextMacroScope_412_);
lean_inc(v_env_411_);
lean_dec(v___x_408_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_446_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_asyncMode_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v_asyncMode_422_ = lean_ctor_get(v_toEnvExtension_410_, 2);
lean_inc(v_asyncMode_422_);
lean_inc(v_decl_399_);
v___x_423_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_409_, v_env_411_, v_decl_399_, v_asyncMode_422_, v_decl_399_);
lean_dec(v_asyncMode_422_);
v___x_424_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 5, v___x_424_);
lean_ctor_set(v___x_420_, 0, v___x_423_);
v___x_426_ = v___x_420_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_nextMacroScope_412_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_ngen_413_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_auxDeclNGen_414_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_traceState_415_);
lean_ctor_set(v_reuseFailAlloc_445_, 5, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_445_, 6, v_messages_416_);
lean_ctor_set(v_reuseFailAlloc_445_, 7, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_445_, 8, v_snapshotTasks_418_);
v___x_426_ = v_reuseFailAlloc_445_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_mctx_429_; lean_object* v_zetaDeltaFVarIds_430_; lean_object* v_postponed_431_; lean_object* v_diag_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_443_; 
v___x_427_ = lean_st_ref_set(v___y_407_, v___x_426_);
v___x_428_ = lean_st_ref_take(v___y_406_);
v_mctx_429_ = lean_ctor_get(v___x_428_, 0);
v_zetaDeltaFVarIds_430_ = lean_ctor_get(v___x_428_, 2);
v_postponed_431_ = lean_ctor_get(v___x_428_, 3);
v_diag_432_ = lean_ctor_get(v___x_428_, 4);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; 
v_unused_444_ = lean_ctor_get(v___x_428_, 1);
lean_dec(v_unused_444_);
v___x_434_ = v___x_428_;
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_diag_432_);
lean_inc(v_postponed_431_);
lean_inc(v_zetaDeltaFVarIds_430_);
lean_inc(v_mctx_429_);
lean_dec(v___x_428_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_mctx_429_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_zetaDeltaFVarIds_430_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_postponed_431_);
lean_ctor_set(v_reuseFailAlloc_442_, 4, v_diag_432_);
v___x_438_ = v_reuseFailAlloc_442_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_st_ref_set(v___y_406_, v___x_438_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
}
}
}
v___jp_450_:
{
lean_object* v_ext_455_; lean_object* v_toEnvExtension_456_; lean_object* v_attr_457_; lean_object* v_asyncMode_458_; uint8_t v___x_459_; 
v_ext_455_ = lean_ctor_get(v_attr_398_, 1);
v_toEnvExtension_456_ = lean_ctor_get(v_ext_455_, 0);
v_attr_457_ = lean_ctor_get(v_attr_398_, 0);
v_asyncMode_458_ = lean_ctor_get(v_toEnvExtension_456_, 2);
lean_inc(v_decl_399_);
lean_inc_ref(v_env_449_);
v___x_459_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_449_, v_decl_399_, v_asyncMode_458_);
if (v___x_459_ == 0)
{
lean_object* v_toAttributeImplCore_460_; lean_object* v_name_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc_ref(v_attr_457_);
lean_dec_ref(v_attr_398_);
v_toAttributeImplCore_460_ = lean_ctor_get(v_attr_457_, 0);
lean_inc_ref(v_toAttributeImplCore_460_);
lean_dec_ref(v_attr_457_);
v_name_461_ = lean_ctor_get(v_toAttributeImplCore_460_, 1);
lean_inc(v_name_461_);
lean_dec_ref(v_toAttributeImplCore_460_);
v___x_462_ = l_Lean_Environment_asyncPrefix_x3f(v_env_449_);
v___x_463_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_name_461_, v_decl_399_, v___x_462_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
return v___x_463_;
}
else
{
lean_dec_ref(v_env_449_);
v___y_406_ = v___y_452_;
v___y_407_ = v___y_454_;
goto v___jp_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object* v_attr_469_, lean_object* v_decl_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v_attr_469_, v_decl_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(lean_object* v_keys_477_, lean_object* v_vals_478_, lean_object* v_i_479_, lean_object* v_k_480_){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_array_get_size(v_keys_477_);
v___x_482_ = lean_nat_dec_lt(v_i_479_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec(v_i_479_);
v___x_483_ = lean_box(0);
return v___x_483_;
}
else
{
lean_object* v_k_x27_484_; uint8_t v___x_485_; 
v_k_x27_484_ = lean_array_fget_borrowed(v_keys_477_, v_i_479_);
v___x_485_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_k_480_, v_k_x27_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_i_479_, v___x_486_);
lean_dec(v_i_479_);
v_i_479_ = v___x_487_;
goto _start;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_array_fget_borrowed(v_vals_478_, v_i_479_);
lean_dec(v_i_479_);
lean_inc(v___x_489_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_keys_491_, lean_object* v_vals_492_, lean_object* v_i_493_, lean_object* v_k_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_491_, v_vals_492_, v_i_493_, v_k_494_);
lean_dec_ref(v_k_494_);
lean_dec_ref(v_vals_492_);
lean_dec_ref(v_keys_491_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(lean_object* v_x_496_, size_t v_x_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v_es_499_; lean_object* v___x_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v_j_503_; lean_object* v___x_504_; 
v_es_499_ = lean_ctor_get(v_x_496_, 0);
v___x_500_ = lean_box(2);
v___x_501_ = ((size_t)31ULL);
v___x_502_ = lean_usize_land(v_x_497_, v___x_501_);
v_j_503_ = lean_usize_to_nat(v___x_502_);
v___x_504_ = lean_array_get_borrowed(v___x_500_, v_es_499_, v_j_503_);
lean_dec(v_j_503_);
switch(lean_obj_tag(v___x_504_))
{
case 0:
{
lean_object* v_key_505_; lean_object* v_val_506_; uint8_t v___x_507_; 
v_key_505_ = lean_ctor_get(v___x_504_, 0);
v_val_506_ = lean_ctor_get(v___x_504_, 1);
v___x_507_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_498_, v_key_505_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_box(0);
return v___x_508_;
}
else
{
lean_object* v___x_509_; 
lean_inc(v_val_506_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v_val_506_);
return v___x_509_;
}
}
case 1:
{
lean_object* v_node_510_; size_t v___x_511_; size_t v___x_512_; 
v_node_510_ = lean_ctor_get(v___x_504_, 0);
v___x_511_ = ((size_t)5ULL);
v___x_512_ = lean_usize_shift_right(v_x_497_, v___x_511_);
v_x_496_ = v_node_510_;
v_x_497_ = v___x_512_;
goto _start;
}
default: 
{
lean_object* v___x_514_; 
v___x_514_ = lean_box(0);
return v___x_514_;
}
}
}
else
{
lean_object* v_ks_515_; lean_object* v_vs_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_ks_515_ = lean_ctor_get(v_x_496_, 0);
v_vs_516_ = lean_ctor_get(v_x_496_, 1);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_ks_515_, v_vs_516_, v___x_517_, v_x_498_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
size_t v_x_6693__boxed_522_; lean_object* v_res_523_; 
v_x_6693__boxed_522_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_res_523_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_519_, v_x_6693__boxed_522_, v_x_521_);
lean_dec_ref(v_x_521_);
lean_dec_ref(v_x_519_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
uint64_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v___x_526_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_525_);
v___x_527_ = lean_uint64_to_usize(v___x_526_);
v___x_528_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_524_, v___x_527_, v_x_525_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg___boxed(lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_529_, v_x_530_);
lean_dec_ref(v_x_530_);
lean_dec_ref(v_x_529_);
return v_res_531_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
if (lean_obj_tag(v_x_533_) == 0)
{
uint8_t v___x_534_; 
v___x_534_ = 1;
return v___x_534_;
}
else
{
uint8_t v___x_535_; 
v___x_535_ = 0;
return v___x_535_;
}
}
else
{
if (lean_obj_tag(v_x_533_) == 0)
{
uint8_t v___x_536_; 
v___x_536_ = 0;
return v___x_536_;
}
else
{
lean_object* v_head_537_; lean_object* v_tail_538_; lean_object* v_head_539_; lean_object* v_tail_540_; uint8_t v___x_541_; 
v_head_537_ = lean_ctor_get(v_x_532_, 0);
v_tail_538_ = lean_ctor_get(v_x_532_, 1);
v_head_539_ = lean_ctor_get(v_x_533_, 0);
v_tail_540_ = lean_ctor_get(v_x_533_, 1);
v___x_541_ = lean_name_eq(v_head_537_, v_head_539_);
if (v___x_541_ == 0)
{
return v___x_541_;
}
else
{
v_x_532_ = v_tail_538_;
v_x_533_ = v_tail_540_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_x_543_, v_x_544_);
lean_dec(v_x_544_);
lean_dec(v_x_543_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object* v_levelParams_550_, lean_object* v_type_551_, lean_object* v_value_552_, lean_object* v_kind_x3f_553_, uint8_t v_cache_554_, uint8_t v_inferRfl_555_, uint8_t v_forceExpose_556_, uint8_t v_defeq_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_563_; lean_object* v_env_564_; lean_object* v___x_565_; lean_object* v_asyncMode_566_; uint8_t v_isExporting_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_651_; lean_object* v___y_652_; uint8_t v___y_653_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; uint8_t v___y_757_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_805_; 
v___x_563_ = lean_st_ref_get(v_a_561_);
v_env_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_ref_n(v_env_564_, 2);
lean_dec(v___x_563_);
v___x_565_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_566_ = lean_ctor_get(v___x_565_, 2);
v_isExporting_567_ = lean_ctor_get_uint8(v_env_564_, sizeof(void*)*8);
v___x_568_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_569_ = lean_box(0);
v___x_770_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_568_, v___x_565_, v_env_564_, v_asyncMode_566_, v___x_569_);
v___x_771_ = lean_bool_not(v_isExporting_567_);
lean_inc_ref(v_type_551_);
v___x_772_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_772_, 0, v_type_551_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*1, v___x_771_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*1 + 1, v_defeq_557_);
if (lean_obj_tag(v_kind_x3f_553_) == 0)
{
lean_object* v___x_823_; 
v___x_823_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__1));
v___y_805_ = v___x_823_;
goto v___jp_804_;
}
else
{
lean_object* v_val_824_; 
v_val_824_ = lean_ctor_get(v_kind_x3f_553_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v_kind_x3f_553_, 1);
v___y_805_ = v_val_824_;
goto v___jp_804_;
}
v___jp_570_:
{
lean_object* v___x_575_; lean_object* v_env_576_; lean_object* v_nextMacroScope_577_; lean_object* v_ngen_578_; lean_object* v_auxDeclNGen_579_; lean_object* v_traceState_580_; lean_object* v_messages_581_; lean_object* v_infoState_582_; lean_object* v_snapshotTasks_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_609_; 
v___x_575_ = lean_st_ref_take(v___y_574_);
v_env_576_ = lean_ctor_get(v___x_575_, 0);
v_nextMacroScope_577_ = lean_ctor_get(v___x_575_, 1);
v_ngen_578_ = lean_ctor_get(v___x_575_, 2);
v_auxDeclNGen_579_ = lean_ctor_get(v___x_575_, 3);
v_traceState_580_ = lean_ctor_get(v___x_575_, 4);
v_messages_581_ = lean_ctor_get(v___x_575_, 6);
v_infoState_582_ = lean_ctor_get(v___x_575_, 7);
v_snapshotTasks_583_ = lean_ctor_get(v___x_575_, 8);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_575_, 5);
lean_dec(v_unused_610_);
v___x_585_ = v___x_575_;
v_isShared_586_ = v_isSharedCheck_609_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_snapshotTasks_583_);
lean_inc(v_infoState_582_);
lean_inc(v_messages_581_);
lean_inc(v_traceState_580_);
lean_inc(v_auxDeclNGen_579_);
lean_inc(v_ngen_578_);
lean_inc(v_nextMacroScope_577_);
lean_inc(v_env_576_);
lean_dec(v___x_575_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_609_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_587_ = l_Lean_EnvExtension_modifyState___redArg(v___x_565_, v_env_576_, v___y_571_, v_asyncMode_566_, v___x_569_);
v___x_588_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 5, v___x_588_);
lean_ctor_set(v___x_585_, 0, v___x_587_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_nextMacroScope_577_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_ngen_578_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_auxDeclNGen_579_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_traceState_580_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_messages_581_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_infoState_582_);
lean_ctor_set(v_reuseFailAlloc_608_, 8, v_snapshotTasks_583_);
v___x_590_ = v_reuseFailAlloc_608_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_mctx_593_; lean_object* v_zetaDeltaFVarIds_594_; lean_object* v_postponed_595_; lean_object* v_diag_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_606_; 
v___x_591_ = lean_st_ref_set(v___y_574_, v___x_590_);
v___x_592_ = lean_st_ref_take(v___y_573_);
v_mctx_593_ = lean_ctor_get(v___x_592_, 0);
v_zetaDeltaFVarIds_594_ = lean_ctor_get(v___x_592_, 2);
v_postponed_595_ = lean_ctor_get(v___x_592_, 3);
v_diag_596_ = lean_ctor_get(v___x_592_, 4);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_592_, 1);
lean_dec(v_unused_607_);
v___x_598_ = v___x_592_;
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_diag_596_);
lean_inc(v_postponed_595_);
lean_inc(v_zetaDeltaFVarIds_594_);
lean_inc(v_mctx_593_);
lean_dec(v___x_592_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_mctx_593_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_zetaDeltaFVarIds_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_postponed_595_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_diag_596_);
v___x_602_ = v_reuseFailAlloc_605_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_st_ref_set(v___y_573_, v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___y_572_);
return v___x_604_;
}
}
}
}
}
v___jp_611_:
{
if (v_inferRfl_555_ == 0)
{
v___y_571_ = v___y_612_;
v___y_572_ = v___y_613_;
v___y_573_ = v___y_615_;
v___y_574_ = v___y_617_;
goto v___jp_570_;
}
else
{
lean_object* v___x_618_; 
lean_inc(v___y_613_);
v___x_618_ = l_Lean_inferDefEqAttr(v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_dec_ref_known(v___x_618_, 1);
v___y_571_ = v___y_612_;
v___y_572_ = v___y_613_;
v___y_573_ = v___y_615_;
v___y_574_ = v___y_617_;
goto v___jp_570_;
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
v___jp_627_:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_addDecl(v___y_630_, v_forceExpose_556_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_dec_ref_known(v___x_631_, 1);
if (v_defeq_557_ == 0)
{
v___y_612_ = v___y_628_;
v___y_613_ = v___y_629_;
v___y_614_ = v_a_558_;
v___y_615_ = v_a_559_;
v___y_616_ = v_a_560_;
v___y_617_ = v_a_561_;
goto v___jp_611_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = l_Lean_defeqAttr;
lean_inc(v___y_629_);
v___x_633_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_632_, v___y_629_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_dec_ref_known(v___x_633_, 1);
v___y_612_ = v___y_628_;
v___y_613_ = v___y_629_;
v___y_614_ = v_a_558_;
v___y_615_ = v_a_559_;
v___y_616_ = v_a_560_;
v___y_617_ = v_a_561_;
goto v___jp_611_;
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
v_a_642_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_631_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_631_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
v___jp_650_:
{
if (v___y_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_inc_n(v___y_652_, 2);
v___x_654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_654_, 0, v___y_652_);
lean_ctor_set(v___x_654_, 1, v_levelParams_550_);
lean_ctor_set(v___x_654_, 2, v_type_551_);
v___x_655_ = lean_box(0);
v___x_656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_656_, 0, v___y_652_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_657_, 0, v___x_654_);
lean_ctor_set(v___x_657_, 1, v_value_552_);
lean_ctor_set(v___x_657_, 2, v___x_656_);
v___x_658_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
v___y_628_ = v___y_651_;
v___y_629_ = v___y_652_;
v___y_630_ = v___x_658_;
goto v___jp_627_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_inc_n(v___y_652_, 2);
v___x_659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_659_, 0, v___y_652_);
lean_ctor_set(v___x_659_, 1, v_levelParams_550_);
lean_ctor_set(v___x_659_, 2, v_type_551_);
v___x_660_ = lean_box(0);
v___x_661_ = 0;
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v___y_652_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_664_, 0, v___x_659_);
lean_ctor_set(v___x_664_, 1, v_value_552_);
lean_ctor_set(v___x_664_, 2, v___x_660_);
lean_ctor_set(v___x_664_, 3, v___x_663_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*4, v___x_661_);
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
v___y_628_ = v___y_651_;
v___y_629_ = v___y_652_;
v___y_630_ = v___x_665_;
goto v___jp_627_;
}
}
v___jp_666_:
{
lean_object* v___x_671_; lean_object* v_env_672_; lean_object* v_nextMacroScope_673_; lean_object* v_ngen_674_; lean_object* v_auxDeclNGen_675_; lean_object* v_traceState_676_; lean_object* v_messages_677_; lean_object* v_infoState_678_; lean_object* v_snapshotTasks_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_705_; 
v___x_671_ = lean_st_ref_take(v___y_670_);
v_env_672_ = lean_ctor_get(v___x_671_, 0);
v_nextMacroScope_673_ = lean_ctor_get(v___x_671_, 1);
v_ngen_674_ = lean_ctor_get(v___x_671_, 2);
v_auxDeclNGen_675_ = lean_ctor_get(v___x_671_, 3);
v_traceState_676_ = lean_ctor_get(v___x_671_, 4);
v_messages_677_ = lean_ctor_get(v___x_671_, 6);
v_infoState_678_ = lean_ctor_get(v___x_671_, 7);
v_snapshotTasks_679_ = lean_ctor_get(v___x_671_, 8);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v___x_671_, 5);
lean_dec(v_unused_706_);
v___x_681_ = v___x_671_;
v_isShared_682_ = v_isSharedCheck_705_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snapshotTasks_679_);
lean_inc(v_infoState_678_);
lean_inc(v_messages_677_);
lean_inc(v_traceState_676_);
lean_inc(v_auxDeclNGen_675_);
lean_inc(v_ngen_674_);
lean_inc(v_nextMacroScope_673_);
lean_inc(v_env_672_);
lean_dec(v___x_671_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_705_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_683_ = l_Lean_EnvExtension_modifyState___redArg(v___x_565_, v_env_672_, v___y_668_, v_asyncMode_566_, v___x_569_);
v___x_684_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 5, v___x_684_);
lean_ctor_set(v___x_681_, 0, v___x_683_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_nextMacroScope_673_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_ngen_674_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_auxDeclNGen_675_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v_traceState_676_);
lean_ctor_set(v_reuseFailAlloc_704_, 5, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_704_, 6, v_messages_677_);
lean_ctor_set(v_reuseFailAlloc_704_, 7, v_infoState_678_);
lean_ctor_set(v_reuseFailAlloc_704_, 8, v_snapshotTasks_679_);
v___x_686_ = v_reuseFailAlloc_704_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_mctx_689_; lean_object* v_zetaDeltaFVarIds_690_; lean_object* v_postponed_691_; lean_object* v_diag_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_702_; 
v___x_687_ = lean_st_ref_set(v___y_670_, v___x_686_);
v___x_688_ = lean_st_ref_take(v___y_669_);
v_mctx_689_ = lean_ctor_get(v___x_688_, 0);
v_zetaDeltaFVarIds_690_ = lean_ctor_get(v___x_688_, 2);
v_postponed_691_ = lean_ctor_get(v___x_688_, 3);
v_diag_692_ = lean_ctor_get(v___x_688_, 4);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v___x_688_, 1);
lean_dec(v_unused_703_);
v___x_694_ = v___x_688_;
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_diag_692_);
lean_inc(v_postponed_691_);
lean_inc(v_zetaDeltaFVarIds_690_);
lean_inc(v_mctx_689_);
lean_dec(v___x_688_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_mctx_689_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_zetaDeltaFVarIds_690_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_postponed_691_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_diag_692_);
v___x_698_ = v_reuseFailAlloc_701_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_st_ref_set(v___y_669_, v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___y_667_);
return v___x_700_;
}
}
}
}
}
v___jp_707_:
{
if (v_inferRfl_555_ == 0)
{
v___y_667_ = v___y_708_;
v___y_668_ = v___y_709_;
v___y_669_ = v___y_711_;
v___y_670_ = v___y_713_;
goto v___jp_666_;
}
else
{
lean_object* v___x_714_; 
lean_inc(v___y_708_);
v___x_714_ = l_Lean_inferDefEqAttr(v___y_708_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_dec_ref_known(v___x_714_, 1);
v___y_667_ = v___y_708_;
v___y_668_ = v___y_709_;
v___y_669_ = v___y_711_;
v___y_670_ = v___y_713_;
goto v___jp_666_;
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
v___jp_723_:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_addDecl(v___y_730_, v_forceExpose_556_, v___y_729_, v___y_725_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_dec_ref_known(v___x_731_, 1);
if (v_defeq_557_ == 0)
{
v___y_708_ = v___y_724_;
v___y_709_ = v___y_726_;
v___y_710_ = v___y_728_;
v___y_711_ = v___y_727_;
v___y_712_ = v___y_729_;
v___y_713_ = v___y_725_;
goto v___jp_707_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = l_Lean_defeqAttr;
lean_inc(v___y_724_);
v___x_733_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_732_, v___y_724_, v___y_728_, v___y_727_, v___y_729_, v___y_725_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_dec_ref_known(v___x_733_, 1);
v___y_708_ = v___y_724_;
v___y_709_ = v___y_726_;
v___y_710_ = v___y_728_;
v___y_711_ = v___y_727_;
v___y_712_ = v___y_729_;
v___y_713_ = v___y_725_;
goto v___jp_707_;
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec_ref(v___y_726_);
lean_dec(v___y_724_);
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v___y_726_);
lean_dec(v___y_724_);
v_a_742_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_731_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_731_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
v___jp_750_:
{
if (v___y_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_inc_n(v___y_752_, 2);
v___x_758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_758_, 0, v___y_752_);
lean_ctor_set(v___x_758_, 1, v_levelParams_550_);
lean_ctor_set(v___x_758_, 2, v_type_551_);
v___x_759_ = lean_box(0);
v___x_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_760_, 0, v___y_752_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
lean_ctor_set(v___x_761_, 1, v_value_552_);
lean_ctor_set(v___x_761_, 2, v___x_760_);
v___x_762_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___y_724_ = v___y_752_;
v___y_725_ = v___y_751_;
v___y_726_ = v___y_753_;
v___y_727_ = v___y_754_;
v___y_728_ = v___y_755_;
v___y_729_ = v___y_756_;
v___y_730_ = v___x_762_;
goto v___jp_723_;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_inc_n(v___y_752_, 2);
v___x_763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_763_, 0, v___y_752_);
lean_ctor_set(v___x_763_, 1, v_levelParams_550_);
lean_ctor_set(v___x_763_, 2, v_type_551_);
v___x_764_ = lean_box(0);
v___x_765_ = 0;
v___x_766_ = lean_box(0);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___y_752_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_768_, 0, v___x_763_);
lean_ctor_set(v___x_768_, 1, v_value_552_);
lean_ctor_set(v___x_768_, 2, v___x_764_);
lean_ctor_set(v___x_768_, 3, v___x_767_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*4, v___x_765_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
v___y_724_ = v___y_752_;
v___y_725_ = v___y_751_;
v___y_726_ = v___y_753_;
v___y_727_ = v___y_754_;
v___y_728_ = v___y_755_;
v___y_729_ = v___y_756_;
v___y_730_ = v___x_769_;
goto v___jp_723_;
}
}
v___jp_773_:
{
lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___f_781_; uint8_t v___x_782_; 
v___x_779_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_774_, v___y_778_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc_n(v_a_780_, 2);
lean_dec_ref(v___x_779_);
lean_inc(v_levelParams_550_);
v___f_781_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_781_, 0, v_a_780_);
lean_closure_set(v___f_781_, 1, v_levelParams_550_);
lean_closure_set(v___f_781_, 2, v___x_772_);
lean_inc_ref(v_env_564_);
v___x_782_ = l_Lean_Environment_hasUnsafe(v_env_564_, v_type_551_);
if (v___x_782_ == 0)
{
uint8_t v___x_783_; 
v___x_783_ = l_Lean_Environment_hasUnsafe(v_env_564_, v_value_552_);
v___y_751_ = v___y_778_;
v___y_752_ = v_a_780_;
v___y_753_ = v___f_781_;
v___y_754_ = v___y_776_;
v___y_755_ = v___y_775_;
v___y_756_ = v___y_777_;
v___y_757_ = v___x_783_;
goto v___jp_750_;
}
else
{
lean_dec_ref(v_env_564_);
v___y_751_ = v___y_778_;
v___y_752_ = v_a_780_;
v___y_753_ = v___f_781_;
v___y_754_ = v___y_776_;
v___y_755_ = v___y_775_;
v___y_756_ = v___y_777_;
v___y_757_ = v___x_782_;
goto v___jp_750_;
}
}
v___jp_784_:
{
if (v___x_771_ == 0)
{
lean_dec(v___x_770_);
v___y_774_ = v___y_785_;
v___y_775_ = v___y_786_;
v___y_776_ = v___y_787_;
v___y_777_ = v___y_788_;
v___y_778_ = v___y_789_;
goto v___jp_773_;
}
else
{
uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = 0;
lean_inc_ref(v_type_551_);
v___x_791_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_791_, 0, v_type_551_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*1, v___x_790_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*1 + 1, v_defeq_557_);
v___x_792_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_770_, v___x_791_);
lean_dec_ref_known(v___x_791_, 1);
lean_dec(v___x_770_);
if (lean_obj_tag(v___x_792_) == 1)
{
lean_object* v_val_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_803_; 
v_val_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_803_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_val_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_fst_797_; lean_object* v_snd_798_; uint8_t v___x_799_; 
v_fst_797_ = lean_ctor_get(v_val_793_, 0);
lean_inc(v_fst_797_);
v_snd_798_ = lean_ctor_get(v_val_793_, 1);
lean_inc(v_snd_798_);
lean_dec(v_val_793_);
v___x_799_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_550_, v_snd_798_);
lean_dec(v_snd_798_);
if (v___x_799_ == 0)
{
lean_dec(v_fst_797_);
lean_del_object(v___x_795_);
v___y_774_ = v___y_785_;
v___y_775_ = v___y_786_;
v___y_776_ = v___y_787_;
v___y_777_ = v___y_788_;
v___y_778_ = v___y_789_;
goto v___jp_773_;
}
else
{
lean_object* v___x_801_; 
lean_dec(v___y_785_);
lean_dec_ref_known(v___x_772_, 1);
lean_dec_ref(v_env_564_);
lean_dec_ref(v_value_552_);
lean_dec_ref(v_type_551_);
lean_dec(v_levelParams_550_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 0);
lean_ctor_set(v___x_795_, 0, v_fst_797_);
v___x_801_ = v___x_795_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_fst_797_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_dec(v___x_792_);
v___y_774_ = v___y_785_;
v___y_775_ = v___y_786_;
v___y_776_ = v___y_787_;
v___y_777_ = v___y_788_;
v___y_778_ = v___y_789_;
goto v___jp_773_;
}
}
}
v___jp_804_:
{
if (v_cache_554_ == 0)
{
lean_object* v___x_806_; lean_object* v_a_807_; lean_object* v___f_808_; uint8_t v___x_809_; 
lean_dec(v___x_770_);
v___x_806_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_805_, v_a_561_);
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc_n(v_a_807_, 2);
lean_dec_ref(v___x_806_);
lean_inc(v_levelParams_550_);
v___f_808_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_808_, 0, v_a_807_);
lean_closure_set(v___f_808_, 1, v_levelParams_550_);
lean_closure_set(v___f_808_, 2, v___x_772_);
lean_inc_ref(v_env_564_);
v___x_809_ = l_Lean_Environment_hasUnsafe(v_env_564_, v_type_551_);
if (v___x_809_ == 0)
{
uint8_t v___x_810_; 
v___x_810_ = l_Lean_Environment_hasUnsafe(v_env_564_, v_value_552_);
v___y_651_ = v___f_808_;
v___y_652_ = v_a_807_;
v___y_653_ = v___x_810_;
goto v___jp_650_;
}
else
{
lean_dec_ref(v_env_564_);
v___y_651_ = v___f_808_;
v___y_652_ = v_a_807_;
v___y_653_ = v___x_809_;
goto v___jp_650_;
}
}
else
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_770_, v___x_772_);
if (lean_obj_tag(v___x_811_) == 1)
{
lean_object* v_val_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_822_; 
v_val_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_822_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_val_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_fst_816_; lean_object* v_snd_817_; uint8_t v___x_818_; 
v_fst_816_ = lean_ctor_get(v_val_812_, 0);
lean_inc(v_fst_816_);
v_snd_817_ = lean_ctor_get(v_val_812_, 1);
lean_inc(v_snd_817_);
lean_dec(v_val_812_);
v___x_818_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_550_, v_snd_817_);
lean_dec(v_snd_817_);
if (v___x_818_ == 0)
{
lean_dec(v_fst_816_);
lean_del_object(v___x_814_);
v___y_785_ = v___y_805_;
v___y_786_ = v_a_558_;
v___y_787_ = v_a_559_;
v___y_788_ = v_a_560_;
v___y_789_ = v_a_561_;
goto v___jp_784_;
}
else
{
lean_object* v___x_820_; 
lean_dec(v___y_805_);
lean_dec_ref_known(v___x_772_, 1);
lean_dec(v___x_770_);
lean_dec_ref(v_env_564_);
lean_dec_ref(v_value_552_);
lean_dec_ref(v_type_551_);
lean_dec(v_levelParams_550_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
lean_ctor_set(v___x_814_, 0, v_fst_816_);
v___x_820_ = v___x_814_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_fst_816_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_dec(v___x_811_);
v___y_785_ = v___y_805_;
v___y_786_ = v_a_558_;
v___y_787_ = v_a_559_;
v___y_788_ = v_a_560_;
v___y_789_ = v_a_561_;
goto v___jp_784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_825_, lean_object* v_type_826_, lean_object* v_value_827_, lean_object* v_kind_x3f_828_, lean_object* v_cache_829_, lean_object* v_inferRfl_830_, lean_object* v_forceExpose_831_, lean_object* v_defeq_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
uint8_t v_cache_boxed_838_; uint8_t v_inferRfl_boxed_839_; uint8_t v_forceExpose_boxed_840_; uint8_t v_defeq_boxed_841_; lean_object* v_res_842_; 
v_cache_boxed_838_ = lean_unbox(v_cache_829_);
v_inferRfl_boxed_839_ = lean_unbox(v_inferRfl_830_);
v_forceExpose_boxed_840_ = lean_unbox(v_forceExpose_831_);
v_defeq_boxed_841_ = lean_unbox(v_defeq_832_);
v_res_842_ = l_Lean_Meta_mkAuxLemma(v_levelParams_825_, v_type_826_, v_value_827_, v_kind_x3f_828_, v_cache_boxed_838_, v_inferRfl_boxed_839_, v_forceExpose_boxed_840_, v_defeq_boxed_841_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_844_, v_x_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_00_u03b2_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_849_, v_x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_00_u03b2_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(v_00_u03b2_852_, v_x_853_, v_x_854_);
lean_dec_ref(v_x_854_);
lean_dec_ref(v_x_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_856_, lean_object* v_x_857_, size_t v_x_858_, size_t v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_857_, v_x_858_, v_x_859_, v_x_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
size_t v_x_7308__boxed_869_; size_t v_x_7309__boxed_870_; lean_object* v_res_871_; 
v_x_7308__boxed_869_ = lean_unbox_usize(v_x_865_);
lean_dec(v_x_865_);
v_x_7309__boxed_870_ = lean_unbox_usize(v_x_866_);
lean_dec(v_x_866_);
v_res_871_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_863_, v_x_864_, v_x_7308__boxed_869_, v_x_7309__boxed_870_, v_x_867_, v_x_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b1_872_, lean_object* v_attrName_873_, lean_object* v_declName_874_, lean_object* v_asyncPrefix_x3f_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_873_, v_declName_874_, v_asyncPrefix_x3f_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_882_, lean_object* v_attrName_883_, lean_object* v_declName_884_, lean_object* v_asyncPrefix_x3f_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b1_882_, v_attrName_883_, v_declName_884_, v_asyncPrefix_x3f_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(lean_object* v_00_u03b1_892_, lean_object* v_attrName_893_, lean_object* v_declName_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_893_, v_declName_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___boxed(lean_object* v_00_u03b1_901_, lean_object* v_attrName_902_, lean_object* v_declName_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(v_00_u03b1_901_, v_attrName_902_, v_declName_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object* v_00_u03b2_910_, lean_object* v_x_911_, size_t v_x_912_, lean_object* v_x_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_911_, v_x_912_, v_x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object* v_00_u03b2_915_, lean_object* v_x_916_, lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
size_t v_x_7359__boxed_919_; lean_object* v_res_920_; 
v_x_7359__boxed_919_ = lean_unbox_usize(v_x_917_);
lean_dec(v_x_917_);
v_res_920_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(v_00_u03b2_915_, v_x_916_, v_x_7359__boxed_919_, v_x_918_);
lean_dec_ref(v_x_918_);
lean_dec_ref(v_x_916_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_921_, lean_object* v_n_922_, lean_object* v_k_923_, lean_object* v_v_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_922_, v_k_923_, v_v_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_926_, size_t v_depth_927_, lean_object* v_keys_928_, lean_object* v_vals_929_, lean_object* v_heq_930_, lean_object* v_i_931_, lean_object* v_entries_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_927_, v_keys_928_, v_vals_929_, v_i_931_, v_entries_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_934_, lean_object* v_depth_935_, lean_object* v_keys_936_, lean_object* v_vals_937_, lean_object* v_heq_938_, lean_object* v_i_939_, lean_object* v_entries_940_){
_start:
{
size_t v_depth_boxed_941_; lean_object* v_res_942_; 
v_depth_boxed_941_ = lean_unbox_usize(v_depth_935_);
lean_dec(v_depth_935_);
v_res_942_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_934_, v_depth_boxed_941_, v_keys_936_, v_vals_937_, v_heq_938_, v_i_939_, v_entries_940_);
lean_dec_ref(v_vals_937_);
lean_dec_ref(v_keys_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_943_, lean_object* v_msg_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_951_, lean_object* v_msg_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b1_951_, v_msg_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_959_, lean_object* v_keys_960_, lean_object* v_vals_961_, lean_object* v_heq_962_, lean_object* v_i_963_, lean_object* v_k_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_960_, v_vals_961_, v_i_963_, v_k_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_966_, lean_object* v_keys_967_, lean_object* v_vals_968_, lean_object* v_heq_969_, lean_object* v_i_970_, lean_object* v_k_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(v_00_u03b2_966_, v_keys_967_, v_vals_968_, v_heq_969_, v_i_970_, v_k_971_);
lean_dec_ref(v_k_971_);
lean_dec_ref(v_vals_968_);
lean_dec_ref(v_keys_967_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_973_, lean_object* v_x_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_x_974_, v_x_975_, v_x_976_, v_x_977_);
return v___x_978_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_DefEqAttrib(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedAuxLemmas_default = _init_l_Lean_Meta_instInhabitedAuxLemmas_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedAuxLemmas_default);
l_Lean_Meta_instInhabitedAuxLemmas = _init_l_Lean_Meta_instInhabitedAuxLemmas();
lean_mark_persistent(l_Lean_Meta_instInhabitedAuxLemmas);
res = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_auxLemmasExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_auxLemmasExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_DefEqAttrib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_AuxLemma(builtin);
}
#ifdef __cplusplus
}
#endif
