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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_defeqAttr;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
if (v_isPrivate_7_ == 0)
{
if (v_isPrivate_4_ == 0)
{
v___y_10_ = v___x_11_;
goto v___jp_9_;
}
else
{
return v_isPrivate_7_;
}
}
else
{
v___y_10_ = v_isPrivate_4_;
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
if (v_defeq_8_ == 0)
{
if (v_defeq_5_ == 0)
{
return v___y_10_;
}
else
{
return v_defeq_8_;
}
}
else
{
return v_defeq_5_;
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
v___x_83_ = lean_st_ref_put(v___y_60_, v___x_82_);
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
lean_object* v_ks_193_; lean_object* v_vs_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_212_; 
v_ks_193_ = lean_ctor_get(v_x_142_, 0);
v_vs_194_ = lean_ctor_get(v_x_142_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_212_ == 0)
{
v___x_196_ = v_x_142_;
v_isShared_197_ = v_isSharedCheck_212_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_vs_194_);
lean_inc(v_ks_193_);
lean_dec(v_x_142_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_212_;
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
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_ks_193_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_vs_194_);
v___x_199_ = v_reuseFailAlloc_211_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v_newNode_200_; size_t v___x_201_; uint8_t v___x_202_; 
v_newNode_200_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v___x_199_, v_x_145_, v_x_146_);
v___x_201_ = ((size_t)7ULL);
v___x_202_ = lean_usize_dec_le(v___x_201_, v_x_144_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_203_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_200_);
v___x_204_ = lean_unsigned_to_nat(4u);
v___x_205_ = lean_nat_dec_lt(v___x_203_, v___x_204_);
lean_dec(v___x_203_);
if (v___x_205_ == 0)
{
lean_object* v_ks_206_; lean_object* v_vs_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_ks_206_ = lean_ctor_get(v_newNode_200_, 0);
lean_inc_ref(v_ks_206_);
v_vs_207_ = lean_ctor_get(v_newNode_200_, 1);
lean_inc_ref(v_vs_207_);
lean_dec_ref(v_newNode_200_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0);
v___x_210_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_x_144_, v_ks_206_, v_vs_207_, v___x_208_, v___x_209_);
lean_dec_ref(v_vs_207_);
lean_dec_ref(v_ks_206_);
return v___x_210_;
}
else
{
return v_newNode_200_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t v_depth_213_, lean_object* v_keys_214_, lean_object* v_vals_215_, lean_object* v_i_216_, lean_object* v_entries_217_){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_array_get_size(v_keys_214_);
v___x_219_ = lean_nat_dec_lt(v_i_216_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec(v_i_216_);
return v_entries_217_;
}
else
{
lean_object* v_k_220_; lean_object* v_v_221_; uint64_t v___x_222_; size_t v_h_223_; size_t v___x_224_; lean_object* v___x_225_; size_t v___x_226_; size_t v___x_227_; size_t v___x_228_; size_t v_h_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_k_220_ = lean_array_fget_borrowed(v_keys_214_, v_i_216_);
v_v_221_ = lean_array_fget_borrowed(v_vals_215_, v_i_216_);
v___x_222_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_k_220_);
v_h_223_ = lean_uint64_to_usize(v___x_222_);
v___x_224_ = ((size_t)5ULL);
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = ((size_t)1ULL);
v___x_227_ = lean_usize_sub(v_depth_213_, v___x_226_);
v___x_228_ = lean_usize_mul(v___x_224_, v___x_227_);
v_h_229_ = lean_usize_shift_right(v_h_223_, v___x_228_);
v___x_230_ = lean_nat_add(v_i_216_, v___x_225_);
lean_dec(v_i_216_);
lean_inc(v_v_221_);
lean_inc(v_k_220_);
v___x_231_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_entries_217_, v_h_229_, v_depth_213_, v_k_220_, v_v_221_);
v_i_216_ = v___x_230_;
v_entries_217_ = v___x_231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_233_, lean_object* v_keys_234_, lean_object* v_vals_235_, lean_object* v_i_236_, lean_object* v_entries_237_){
_start:
{
size_t v_depth_boxed_238_; lean_object* v_res_239_; 
v_depth_boxed_238_ = lean_unbox_usize(v_depth_233_);
lean_dec(v_depth_233_);
v_res_239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_boxed_238_, v_keys_234_, v_vals_235_, v_i_236_, v_entries_237_);
lean_dec_ref(v_vals_235_);
lean_dec_ref(v_keys_234_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
size_t v_x_5302__boxed_245_; size_t v_x_5303__boxed_246_; lean_object* v_res_247_; 
v_x_5302__boxed_245_ = lean_unbox_usize(v_x_241_);
lean_dec(v_x_241_);
v_x_5303__boxed_246_ = lean_unbox_usize(v_x_242_);
lean_dec(v_x_242_);
v_res_247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_240_, v_x_5302__boxed_245_, v_x_5303__boxed_246_, v_x_243_, v_x_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
uint64_t v___x_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v___x_254_; 
v___x_251_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_249_);
v___x_252_ = lean_uint64_to_usize(v___x_251_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_248_, v___x_252_, v___x_253_, v_x_249_, v_x_250_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object* v_a_255_, lean_object* v_levelParams_256_, lean_object* v___x_257_, lean_object* v_x_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_a_255_);
lean_ctor_set(v___x_259_, 1, v_levelParams_256_);
v___x_260_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_258_, v___x_257_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(lean_object* v_msgData_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; lean_object* v_env_268_; lean_object* v___x_269_; lean_object* v_toCold_270_; lean_object* v_mctx_271_; lean_object* v_lctx_272_; lean_object* v_options_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_267_ = lean_st_ref_get(v___y_265_);
v_env_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_env_268_);
lean_dec(v___x_267_);
v___x_269_ = lean_st_ref_get(v___y_263_);
v_toCold_270_ = lean_ctor_get(v___y_264_, 0);
v_mctx_271_ = lean_ctor_get(v___x_269_, 0);
lean_inc_ref(v_mctx_271_);
lean_dec(v___x_269_);
v_lctx_272_ = lean_ctor_get(v___y_262_, 2);
v_options_273_ = lean_ctor_get(v_toCold_270_, 2);
lean_inc_ref(v_options_273_);
lean_inc_ref(v_lctx_272_);
v___x_274_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_274_, 0, v_env_268_);
lean_ctor_set(v___x_274_, 1, v_mctx_271_);
lean_ctor_set(v___x_274_, 2, v_lctx_272_);
lean_ctor_set(v___x_274_, 3, v_options_273_);
v___x_275_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v_msgData_261_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_msgData_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msgData_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(lean_object* v_msg_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_ref_290_; lean_object* v___x_291_; lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_300_; 
v_ref_290_ = lean_ctor_get(v___y_287_, 2);
v___x_291_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msg_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_300_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
lean_inc(v_ref_290_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_ref_290_);
lean_ctor_set(v___x_296_, 1, v_a_292_);
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 1);
lean_ctor_set(v___x_294_, 0, v___x_296_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_msg_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_307_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0));
v___x_310_ = l_Lean_stringToMessageData(v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2));
v___x_313_ = l_Lean_stringToMessageData(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4));
v___x_316_ = l_Lean_stringToMessageData(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6));
v___x_319_ = l_Lean_stringToMessageData(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8));
v___x_322_ = l_Lean_stringToMessageData(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(lean_object* v_attrName_323_, lean_object* v_declName_324_, lean_object* v_asyncPrefix_x3f_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___y_332_; 
if (lean_obj_tag(v_asyncPrefix_x3f_325_) == 0)
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_MessageData_nil;
v___y_332_ = v___x_345_;
goto v___jp_331_;
}
else
{
lean_object* v_val_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_val_346_ = lean_ctor_get(v_asyncPrefix_x3f_325_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v_asyncPrefix_x3f_325_, 1);
v___x_347_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7);
v___x_348_ = l_Lean_MessageData_ofName(v_val_346_);
v___x_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9);
v___x_351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___y_332_ = v___x_351_;
goto v___jp_331_;
}
v___jp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_333_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_334_ = l_Lean_MessageData_ofName(v_attrName_323_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = 0;
v___x_339_ = l_Lean_MessageData_ofConstName(v_declName_324_, v___x_338_);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_337_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___y_332_);
v___x_344_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_343_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object* v_attrName_352_, lean_object* v_declName_353_, lean_object* v_asyncPrefix_x3f_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_352_, v_declName_353_, v_asyncPrefix_x3f_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_360_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(lean_object* v_attrName_364_, lean_object* v_declName_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_371_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_372_ = l_Lean_MessageData_ofName(v_attrName_364_);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = 0;
v___x_377_ = l_Lean_MessageData_ofConstName(v_declName_365_, v___x_376_);
v___x_378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_375_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1);
v___x_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_380_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___boxed(lean_object* v_attrName_382_, lean_object* v_declName_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_382_, v_declName_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_390_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_396_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
lean_ctor_set(v___x_396_, 2, v___x_395_);
lean_ctor_set(v___x_396_, 3, v___x_395_);
lean_ctor_set(v___x_396_, 4, v___x_395_);
lean_ctor_set(v___x_396_, 5, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object* v_attr_397_, lean_object* v_decl_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___x_447_; lean_object* v_env_448_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___x_463_; 
v___x_447_ = lean_st_ref_get(v___y_402_);
v_env_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc_ref(v_env_448_);
lean_dec(v___x_447_);
v___x_463_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_448_, v_decl_398_);
if (lean_obj_tag(v___x_463_) == 0)
{
v___y_450_ = v___y_399_;
v___y_451_ = v___y_400_;
v___y_452_ = v___y_401_;
v___y_453_ = v___y_402_;
goto v___jp_449_;
}
else
{
lean_object* v_attr_464_; lean_object* v_toAttributeImplCore_465_; lean_object* v_name_466_; lean_object* v___x_467_; 
lean_dec_ref_known(v___x_463_, 1);
lean_dec_ref(v_env_448_);
v_attr_464_ = lean_ctor_get(v_attr_397_, 0);
lean_inc_ref(v_attr_464_);
lean_dec_ref(v_attr_397_);
v_toAttributeImplCore_465_ = lean_ctor_get(v_attr_464_, 0);
lean_inc_ref(v_toAttributeImplCore_465_);
lean_dec_ref(v_attr_464_);
v_name_466_ = lean_ctor_get(v_toAttributeImplCore_465_, 1);
lean_inc(v_name_466_);
lean_dec_ref(v_toAttributeImplCore_465_);
v___x_467_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_name_466_, v_decl_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
return v___x_467_;
}
v___jp_404_:
{
lean_object* v___x_407_; lean_object* v_ext_408_; lean_object* v_toEnvExtension_409_; lean_object* v_env_410_; lean_object* v_nextMacroScope_411_; lean_object* v_ngen_412_; lean_object* v_auxDeclNGen_413_; lean_object* v_traceState_414_; lean_object* v_messages_415_; lean_object* v_infoState_416_; lean_object* v_snapshotTasks_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_445_; 
v___x_407_ = lean_st_ref_take(v___y_406_);
v_ext_408_ = lean_ctor_get(v_attr_397_, 1);
lean_inc_ref(v_ext_408_);
lean_dec_ref(v_attr_397_);
v_toEnvExtension_409_ = lean_ctor_get(v_ext_408_, 0);
v_env_410_ = lean_ctor_get(v___x_407_, 0);
v_nextMacroScope_411_ = lean_ctor_get(v___x_407_, 1);
v_ngen_412_ = lean_ctor_get(v___x_407_, 2);
v_auxDeclNGen_413_ = lean_ctor_get(v___x_407_, 3);
v_traceState_414_ = lean_ctor_get(v___x_407_, 4);
v_messages_415_ = lean_ctor_get(v___x_407_, 6);
v_infoState_416_ = lean_ctor_get(v___x_407_, 7);
v_snapshotTasks_417_ = lean_ctor_get(v___x_407_, 8);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_407_, 5);
lean_dec(v_unused_446_);
v___x_419_ = v___x_407_;
v_isShared_420_ = v_isSharedCheck_445_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_snapshotTasks_417_);
lean_inc(v_infoState_416_);
lean_inc(v_messages_415_);
lean_inc(v_traceState_414_);
lean_inc(v_auxDeclNGen_413_);
lean_inc(v_ngen_412_);
lean_inc(v_nextMacroScope_411_);
lean_inc(v_env_410_);
lean_dec(v___x_407_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_445_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_asyncMode_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v_asyncMode_421_ = lean_ctor_get(v_toEnvExtension_409_, 2);
lean_inc(v_asyncMode_421_);
lean_inc(v_decl_398_);
v___x_422_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_408_, v_env_410_, v_decl_398_, v_asyncMode_421_, v_decl_398_);
lean_dec(v_asyncMode_421_);
v___x_423_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 5, v___x_423_);
lean_ctor_set(v___x_419_, 0, v___x_422_);
v___x_425_ = v___x_419_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_nextMacroScope_411_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_ngen_412_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_auxDeclNGen_413_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_traceState_414_);
lean_ctor_set(v_reuseFailAlloc_444_, 5, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_444_, 6, v_messages_415_);
lean_ctor_set(v_reuseFailAlloc_444_, 7, v_infoState_416_);
lean_ctor_set(v_reuseFailAlloc_444_, 8, v_snapshotTasks_417_);
v___x_425_ = v_reuseFailAlloc_444_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_mctx_428_; lean_object* v_zetaDeltaFVarIds_429_; lean_object* v_postponed_430_; lean_object* v_diag_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_442_; 
v___x_426_ = lean_st_ref_put(v___y_406_, v___x_425_);
v___x_427_ = lean_st_ref_take(v___y_405_);
v_mctx_428_ = lean_ctor_get(v___x_427_, 0);
v_zetaDeltaFVarIds_429_ = lean_ctor_get(v___x_427_, 2);
v_postponed_430_ = lean_ctor_get(v___x_427_, 3);
v_diag_431_ = lean_ctor_get(v___x_427_, 4);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v___x_427_, 1);
lean_dec(v_unused_443_);
v___x_433_ = v___x_427_;
v_isShared_434_ = v_isSharedCheck_442_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_diag_431_);
lean_inc(v_postponed_430_);
lean_inc(v_zetaDeltaFVarIds_429_);
lean_inc(v_mctx_428_);
lean_dec(v___x_427_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_442_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_mctx_428_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_zetaDeltaFVarIds_429_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_postponed_430_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v_diag_431_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_st_ref_put(v___y_405_, v___x_437_);
v___x_439_ = lean_box(0);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
}
}
}
v___jp_449_:
{
lean_object* v_ext_454_; lean_object* v_toEnvExtension_455_; lean_object* v_attr_456_; lean_object* v_asyncMode_457_; uint8_t v___x_458_; 
v_ext_454_ = lean_ctor_get(v_attr_397_, 1);
v_toEnvExtension_455_ = lean_ctor_get(v_ext_454_, 0);
v_attr_456_ = lean_ctor_get(v_attr_397_, 0);
v_asyncMode_457_ = lean_ctor_get(v_toEnvExtension_455_, 2);
lean_inc(v_decl_398_);
lean_inc_ref(v_env_448_);
v___x_458_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_448_, v_decl_398_, v_asyncMode_457_);
if (v___x_458_ == 0)
{
lean_object* v_toAttributeImplCore_459_; lean_object* v_name_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
lean_inc_ref(v_attr_456_);
lean_dec_ref(v_attr_397_);
v_toAttributeImplCore_459_ = lean_ctor_get(v_attr_456_, 0);
lean_inc_ref(v_toAttributeImplCore_459_);
lean_dec_ref(v_attr_456_);
v_name_460_ = lean_ctor_get(v_toAttributeImplCore_459_, 1);
lean_inc(v_name_460_);
lean_dec_ref(v_toAttributeImplCore_459_);
v___x_461_ = l_Lean_Environment_asyncPrefix_x3f(v_env_448_);
v___x_462_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_name_460_, v_decl_398_, v___x_461_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
return v___x_462_;
}
else
{
lean_dec_ref(v_env_448_);
v___y_405_ = v___y_451_;
v___y_406_ = v___y_453_;
goto v___jp_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object* v_attr_468_, lean_object* v_decl_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v_attr_468_, v_decl_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(lean_object* v_keys_476_, lean_object* v_vals_477_, lean_object* v_i_478_, lean_object* v_k_479_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_array_get_size(v_keys_476_);
v___x_481_ = lean_nat_dec_lt(v_i_478_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
lean_dec(v_i_478_);
v___x_482_ = lean_box(0);
return v___x_482_;
}
else
{
lean_object* v_k_x27_483_; uint8_t v___x_484_; 
v_k_x27_483_ = lean_array_fget_borrowed(v_keys_476_, v_i_478_);
v___x_484_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_k_479_, v_k_x27_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_add(v_i_478_, v___x_485_);
lean_dec(v_i_478_);
v_i_478_ = v___x_486_;
goto _start;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_array_fget_borrowed(v_vals_477_, v_i_478_);
lean_dec(v_i_478_);
lean_inc(v___x_488_);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_keys_490_, lean_object* v_vals_491_, lean_object* v_i_492_, lean_object* v_k_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_490_, v_vals_491_, v_i_492_, v_k_493_);
lean_dec_ref(v_k_493_);
lean_dec_ref(v_vals_491_);
lean_dec_ref(v_keys_490_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(lean_object* v_x_495_, size_t v_x_496_, lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v_es_498_; lean_object* v___x_499_; size_t v___x_500_; size_t v___x_501_; lean_object* v_j_502_; lean_object* v___x_503_; 
v_es_498_ = lean_ctor_get(v_x_495_, 0);
v___x_499_ = lean_box(2);
v___x_500_ = ((size_t)31ULL);
v___x_501_ = lean_usize_land(v_x_496_, v___x_500_);
v_j_502_ = lean_usize_to_nat(v___x_501_);
v___x_503_ = lean_array_get_borrowed(v___x_499_, v_es_498_, v_j_502_);
lean_dec(v_j_502_);
switch(lean_obj_tag(v___x_503_))
{
case 0:
{
lean_object* v_key_504_; lean_object* v_val_505_; uint8_t v___x_506_; 
v_key_504_ = lean_ctor_get(v___x_503_, 0);
v_val_505_ = lean_ctor_get(v___x_503_, 1);
v___x_506_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_497_, v_key_504_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_box(0);
return v___x_507_;
}
else
{
lean_object* v___x_508_; 
lean_inc(v_val_505_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v_val_505_);
return v___x_508_;
}
}
case 1:
{
lean_object* v_node_509_; size_t v___x_510_; size_t v___x_511_; 
v_node_509_ = lean_ctor_get(v___x_503_, 0);
v___x_510_ = ((size_t)5ULL);
v___x_511_ = lean_usize_shift_right(v_x_496_, v___x_510_);
v_x_495_ = v_node_509_;
v_x_496_ = v___x_511_;
goto _start;
}
default: 
{
lean_object* v___x_513_; 
v___x_513_ = lean_box(0);
return v___x_513_;
}
}
}
else
{
lean_object* v_ks_514_; lean_object* v_vs_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_ks_514_ = lean_ctor_get(v_x_495_, 0);
v_vs_515_ = lean_ctor_get(v_x_495_, 1);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_ks_514_, v_vs_515_, v___x_516_, v_x_497_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
size_t v_x_5841__boxed_521_; lean_object* v_res_522_; 
v_x_5841__boxed_521_ = lean_unbox_usize(v_x_519_);
lean_dec(v_x_519_);
v_res_522_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_518_, v_x_5841__boxed_521_, v_x_520_);
lean_dec_ref(v_x_520_);
lean_dec_ref(v_x_518_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
uint64_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_524_);
v___x_526_ = lean_uint64_to_usize(v___x_525_);
v___x_527_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_523_, v___x_526_, v_x_524_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg___boxed(lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_528_, v_x_529_);
lean_dec_ref(v_x_529_);
lean_dec_ref(v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
if (lean_obj_tag(v_x_532_) == 0)
{
uint8_t v___x_533_; 
v___x_533_ = 1;
return v___x_533_;
}
else
{
uint8_t v___x_534_; 
v___x_534_ = 0;
return v___x_534_;
}
}
else
{
if (lean_obj_tag(v_x_532_) == 0)
{
uint8_t v___x_535_; 
v___x_535_ = 0;
return v___x_535_;
}
else
{
lean_object* v_head_536_; lean_object* v_tail_537_; lean_object* v_head_538_; lean_object* v_tail_539_; uint8_t v___x_540_; 
v_head_536_ = lean_ctor_get(v_x_531_, 0);
v_tail_537_ = lean_ctor_get(v_x_531_, 1);
v_head_538_ = lean_ctor_get(v_x_532_, 0);
v_tail_539_ = lean_ctor_get(v_x_532_, 1);
v___x_540_ = lean_name_eq(v_head_536_, v_head_538_);
if (v___x_540_ == 0)
{
return v___x_540_;
}
else
{
v_x_531_ = v_tail_537_;
v_x_532_ = v_tail_539_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
uint8_t v_res_544_; lean_object* v_r_545_; 
v_res_544_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_x_542_, v_x_543_);
lean_dec(v_x_543_);
lean_dec(v_x_542_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object* v_levelParams_549_, lean_object* v_type_550_, lean_object* v_value_551_, lean_object* v_kind_x3f_552_, uint8_t v_cache_553_, uint8_t v_inferRfl_554_, uint8_t v_forceExpose_555_, uint8_t v_defeq_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v___x_562_; lean_object* v_env_563_; lean_object* v___x_564_; lean_object* v_asyncMode_565_; uint8_t v_isExporting_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_766_; lean_object* v___y_767_; uint8_t v___y_768_; lean_object* v___x_781_; lean_object* v___y_783_; uint8_t v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_805_; uint8_t v___y_806_; lean_object* v___y_807_; uint8_t v___y_826_; 
v___x_562_ = lean_st_ref_get(v_a_560_);
v_env_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref_n(v_env_563_, 2);
lean_dec(v___x_562_);
v___x_564_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_565_ = lean_ctor_get(v___x_564_, 2);
v_isExporting_566_ = lean_ctor_get_uint8(v_env_563_, sizeof(void*)*8);
v___x_567_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_568_ = lean_box(0);
v___x_781_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_567_, v___x_564_, v_env_563_, v_asyncMode_565_, v___x_568_);
if (v_isExporting_566_ == 0)
{
uint8_t v___x_830_; 
v___x_830_ = 1;
v___y_826_ = v___x_830_;
goto v___jp_825_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = 0;
v___y_826_ = v___x_831_;
goto v___jp_825_;
}
v___jp_569_:
{
lean_object* v___x_574_; lean_object* v_env_575_; lean_object* v_nextMacroScope_576_; lean_object* v_ngen_577_; lean_object* v_auxDeclNGen_578_; lean_object* v_traceState_579_; lean_object* v_messages_580_; lean_object* v_infoState_581_; lean_object* v_snapshotTasks_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_608_; 
v___x_574_ = lean_st_ref_take(v___y_573_);
v_env_575_ = lean_ctor_get(v___x_574_, 0);
v_nextMacroScope_576_ = lean_ctor_get(v___x_574_, 1);
v_ngen_577_ = lean_ctor_get(v___x_574_, 2);
v_auxDeclNGen_578_ = lean_ctor_get(v___x_574_, 3);
v_traceState_579_ = lean_ctor_get(v___x_574_, 4);
v_messages_580_ = lean_ctor_get(v___x_574_, 6);
v_infoState_581_ = lean_ctor_get(v___x_574_, 7);
v_snapshotTasks_582_ = lean_ctor_get(v___x_574_, 8);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_574_, 5);
lean_dec(v_unused_609_);
v___x_584_ = v___x_574_;
v_isShared_585_ = v_isSharedCheck_608_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_snapshotTasks_582_);
lean_inc(v_infoState_581_);
lean_inc(v_messages_580_);
lean_inc(v_traceState_579_);
lean_inc(v_auxDeclNGen_578_);
lean_inc(v_ngen_577_);
lean_inc(v_nextMacroScope_576_);
lean_inc(v_env_575_);
lean_dec(v___x_574_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_608_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_586_ = l_Lean_EnvExtension_modifyState___redArg(v___x_564_, v_env_575_, v___y_570_, v_asyncMode_565_, v___x_568_);
v___x_587_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 5, v___x_587_);
lean_ctor_set(v___x_584_, 0, v___x_586_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_nextMacroScope_576_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_ngen_577_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_auxDeclNGen_578_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_traceState_579_);
lean_ctor_set(v_reuseFailAlloc_607_, 5, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_607_, 6, v_messages_580_);
lean_ctor_set(v_reuseFailAlloc_607_, 7, v_infoState_581_);
lean_ctor_set(v_reuseFailAlloc_607_, 8, v_snapshotTasks_582_);
v___x_589_ = v_reuseFailAlloc_607_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_mctx_592_; lean_object* v_zetaDeltaFVarIds_593_; lean_object* v_postponed_594_; lean_object* v_diag_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_605_; 
v___x_590_ = lean_st_ref_put(v___y_573_, v___x_589_);
v___x_591_ = lean_st_ref_take(v___y_572_);
v_mctx_592_ = lean_ctor_get(v___x_591_, 0);
v_zetaDeltaFVarIds_593_ = lean_ctor_get(v___x_591_, 2);
v_postponed_594_ = lean_ctor_get(v___x_591_, 3);
v_diag_595_ = lean_ctor_get(v___x_591_, 4);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___x_591_, 1);
lean_dec(v_unused_606_);
v___x_597_ = v___x_591_;
v_isShared_598_ = v_isSharedCheck_605_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_diag_595_);
lean_inc(v_postponed_594_);
lean_inc(v_zetaDeltaFVarIds_593_);
lean_inc(v_mctx_592_);
lean_dec(v___x_591_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_605_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_599_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 1, v___x_599_);
v___x_601_ = v___x_597_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_mctx_592_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_zetaDeltaFVarIds_593_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_postponed_594_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v_diag_595_);
v___x_601_ = v_reuseFailAlloc_604_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_st_ref_put(v___y_572_, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___y_571_);
return v___x_603_;
}
}
}
}
}
v___jp_610_:
{
if (v_inferRfl_554_ == 0)
{
v___y_570_ = v___y_611_;
v___y_571_ = v___y_612_;
v___y_572_ = v___y_614_;
v___y_573_ = v___y_616_;
goto v___jp_569_;
}
else
{
lean_object* v___x_617_; 
lean_inc(v___y_612_);
v___x_617_ = l_Lean_inferDefEqAttr(v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_dec_ref_known(v___x_617_, 1);
v___y_570_ = v___y_611_;
v___y_571_ = v___y_612_;
v___y_572_ = v___y_614_;
v___y_573_ = v___y_616_;
goto v___jp_569_;
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
v___jp_626_:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_addDecl(v___y_633_, v_forceExpose_555_, v___y_632_, v___y_630_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_dec_ref_known(v___x_634_, 1);
if (v_defeq_556_ == 0)
{
v___y_611_ = v___y_627_;
v___y_612_ = v___y_628_;
v___y_613_ = v___y_629_;
v___y_614_ = v___y_631_;
v___y_615_ = v___y_632_;
v___y_616_ = v___y_630_;
goto v___jp_610_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = l_Lean_defeqAttr;
lean_inc(v___y_628_);
v___x_636_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_635_, v___y_628_, v___y_629_, v___y_631_, v___y_632_, v___y_630_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_dec_ref_known(v___x_636_, 1);
v___y_611_ = v___y_627_;
v___y_612_ = v___y_628_;
v___y_613_ = v___y_629_;
v___y_614_ = v___y_631_;
v___y_615_ = v___y_632_;
v___y_616_ = v___y_630_;
goto v___jp_610_;
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
v_a_645_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_634_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_634_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
v___jp_653_:
{
if (v___y_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_inc_n(v___y_655_, 2);
v___x_661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_661_, 0, v___y_655_);
lean_ctor_set(v___x_661_, 1, v_levelParams_549_);
lean_ctor_set(v___x_661_, 2, v_type_550_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v___y_655_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_664_, 0, v___x_661_);
lean_ctor_set(v___x_664_, 1, v_value_551_);
lean_ctor_set(v___x_664_, 2, v___x_663_);
v___x_665_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
v___y_627_ = v___y_654_;
v___y_628_ = v___y_655_;
v___y_629_ = v___y_657_;
v___y_630_ = v___y_656_;
v___y_631_ = v___y_658_;
v___y_632_ = v___y_659_;
v___y_633_ = v___x_665_;
goto v___jp_626_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_inc_n(v___y_655_, 2);
v___x_666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_666_, 0, v___y_655_);
lean_ctor_set(v___x_666_, 1, v_levelParams_549_);
lean_ctor_set(v___x_666_, 2, v_type_550_);
v___x_667_ = lean_box(0);
v___x_668_ = 0;
v___x_669_ = lean_box(0);
v___x_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_670_, 0, v___y_655_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_671_, 0, v___x_666_);
lean_ctor_set(v___x_671_, 1, v_value_551_);
lean_ctor_set(v___x_671_, 2, v___x_667_);
lean_ctor_set(v___x_671_, 3, v___x_670_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*4, v___x_668_);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
v___y_627_ = v___y_654_;
v___y_628_ = v___y_655_;
v___y_629_ = v___y_657_;
v___y_630_ = v___y_656_;
v___y_631_ = v___y_658_;
v___y_632_ = v___y_659_;
v___y_633_ = v___x_672_;
goto v___jp_626_;
}
}
v___jp_673_:
{
lean_object* v___x_680_; lean_object* v_a_681_; lean_object* v___f_682_; uint8_t v___x_683_; 
v___x_680_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_675_, v___y_679_);
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc_n(v_a_681_, 2);
lean_dec_ref(v___x_680_);
lean_inc(v_levelParams_549_);
v___f_682_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_682_, 0, v_a_681_);
lean_closure_set(v___f_682_, 1, v_levelParams_549_);
lean_closure_set(v___f_682_, 2, v___y_674_);
lean_inc_ref(v_env_563_);
v___x_683_ = l_Lean_Environment_hasUnsafe(v_env_563_, v_type_550_);
if (v___x_683_ == 0)
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_Environment_hasUnsafe(v_env_563_, v_value_551_);
v___y_654_ = v___f_682_;
v___y_655_ = v_a_681_;
v___y_656_ = v___y_679_;
v___y_657_ = v___y_676_;
v___y_658_ = v___y_677_;
v___y_659_ = v___y_678_;
v___y_660_ = v___x_684_;
goto v___jp_653_;
}
else
{
lean_dec_ref(v_env_563_);
v___y_654_ = v___f_682_;
v___y_655_ = v_a_681_;
v___y_656_ = v___y_679_;
v___y_657_ = v___y_676_;
v___y_658_ = v___y_677_;
v___y_659_ = v___y_678_;
v___y_660_ = v___x_683_;
goto v___jp_653_;
}
}
v___jp_685_:
{
lean_object* v___x_690_; lean_object* v_env_691_; lean_object* v_nextMacroScope_692_; lean_object* v_ngen_693_; lean_object* v_auxDeclNGen_694_; lean_object* v_traceState_695_; lean_object* v_messages_696_; lean_object* v_infoState_697_; lean_object* v_snapshotTasks_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_724_; 
v___x_690_ = lean_st_ref_take(v___y_689_);
v_env_691_ = lean_ctor_get(v___x_690_, 0);
v_nextMacroScope_692_ = lean_ctor_get(v___x_690_, 1);
v_ngen_693_ = lean_ctor_get(v___x_690_, 2);
v_auxDeclNGen_694_ = lean_ctor_get(v___x_690_, 3);
v_traceState_695_ = lean_ctor_get(v___x_690_, 4);
v_messages_696_ = lean_ctor_get(v___x_690_, 6);
v_infoState_697_ = lean_ctor_get(v___x_690_, 7);
v_snapshotTasks_698_ = lean_ctor_get(v___x_690_, 8);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_690_, 5);
lean_dec(v_unused_725_);
v___x_700_ = v___x_690_;
v_isShared_701_ = v_isSharedCheck_724_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_snapshotTasks_698_);
lean_inc(v_infoState_697_);
lean_inc(v_messages_696_);
lean_inc(v_traceState_695_);
lean_inc(v_auxDeclNGen_694_);
lean_inc(v_ngen_693_);
lean_inc(v_nextMacroScope_692_);
lean_inc(v_env_691_);
lean_dec(v___x_690_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_724_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_702_ = l_Lean_EnvExtension_modifyState___redArg(v___x_564_, v_env_691_, v___y_686_, v_asyncMode_565_, v___x_568_);
v___x_703_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 5, v___x_703_);
lean_ctor_set(v___x_700_, 0, v___x_702_);
v___x_705_ = v___x_700_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_nextMacroScope_692_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_ngen_693_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_auxDeclNGen_694_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_traceState_695_);
lean_ctor_set(v_reuseFailAlloc_723_, 5, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_723_, 6, v_messages_696_);
lean_ctor_set(v_reuseFailAlloc_723_, 7, v_infoState_697_);
lean_ctor_set(v_reuseFailAlloc_723_, 8, v_snapshotTasks_698_);
v___x_705_ = v_reuseFailAlloc_723_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_mctx_708_; lean_object* v_zetaDeltaFVarIds_709_; lean_object* v_postponed_710_; lean_object* v_diag_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_721_; 
v___x_706_ = lean_st_ref_put(v___y_689_, v___x_705_);
v___x_707_ = lean_st_ref_take(v___y_688_);
v_mctx_708_ = lean_ctor_get(v___x_707_, 0);
v_zetaDeltaFVarIds_709_ = lean_ctor_get(v___x_707_, 2);
v_postponed_710_ = lean_ctor_get(v___x_707_, 3);
v_diag_711_ = lean_ctor_get(v___x_707_, 4);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v___x_707_, 1);
lean_dec(v_unused_722_);
v___x_713_ = v___x_707_;
v_isShared_714_ = v_isSharedCheck_721_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_diag_711_);
lean_inc(v_postponed_710_);
lean_inc(v_zetaDeltaFVarIds_709_);
lean_inc(v_mctx_708_);
lean_dec(v___x_707_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_721_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_mctx_708_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_zetaDeltaFVarIds_709_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_postponed_710_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_diag_711_);
v___x_717_ = v_reuseFailAlloc_720_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_st_ref_put(v___y_688_, v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___y_687_);
return v___x_719_;
}
}
}
}
}
v___jp_726_:
{
if (v_inferRfl_554_ == 0)
{
v___y_686_ = v___y_727_;
v___y_687_ = v___y_728_;
v___y_688_ = v___y_730_;
v___y_689_ = v___y_732_;
goto v___jp_685_;
}
else
{
lean_object* v___x_733_; 
lean_inc(v___y_728_);
v___x_733_ = l_Lean_inferDefEqAttr(v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_dec_ref_known(v___x_733_, 1);
v___y_686_ = v___y_727_;
v___y_687_ = v___y_728_;
v___y_688_ = v___y_730_;
v___y_689_ = v___y_732_;
goto v___jp_685_;
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
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
v___jp_742_:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_addDecl(v___y_745_, v_forceExpose_555_, v_a_559_, v_a_560_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_dec_ref_known(v___x_746_, 1);
if (v_defeq_556_ == 0)
{
v___y_727_ = v___y_743_;
v___y_728_ = v___y_744_;
v___y_729_ = v_a_557_;
v___y_730_ = v_a_558_;
v___y_731_ = v_a_559_;
v___y_732_ = v_a_560_;
goto v___jp_726_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = l_Lean_defeqAttr;
lean_inc(v___y_744_);
v___x_748_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_747_, v___y_744_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_dec_ref_known(v___x_748_, 1);
v___y_727_ = v___y_743_;
v___y_728_ = v___y_744_;
v___y_729_ = v_a_557_;
v___y_730_ = v_a_558_;
v___y_731_ = v_a_559_;
v___y_732_ = v_a_560_;
goto v___jp_726_;
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
v_a_757_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_746_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_746_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
v___jp_765_:
{
if (v___y_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_inc_n(v___y_767_, 2);
v___x_769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_769_, 0, v___y_767_);
lean_ctor_set(v___x_769_, 1, v_levelParams_549_);
lean_ctor_set(v___x_769_, 2, v_type_550_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_771_, 0, v___y_767_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v___x_769_);
lean_ctor_set(v___x_772_, 1, v_value_551_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
v___x_773_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
v___y_743_ = v___y_766_;
v___y_744_ = v___y_767_;
v___y_745_ = v___x_773_;
goto v___jp_742_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_inc_n(v___y_767_, 2);
v___x_774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_774_, 0, v___y_767_);
lean_ctor_set(v___x_774_, 1, v_levelParams_549_);
lean_ctor_set(v___x_774_, 2, v_type_550_);
v___x_775_ = lean_box(0);
v___x_776_ = 0;
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v___y_767_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_779_, 0, v___x_774_);
lean_ctor_set(v___x_779_, 1, v_value_551_);
lean_ctor_set(v___x_779_, 2, v___x_775_);
lean_ctor_set(v___x_779_, 3, v___x_778_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*4, v___x_776_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
v___y_743_ = v___y_766_;
v___y_744_ = v___y_767_;
v___y_745_ = v___x_780_;
goto v___jp_742_;
}
}
v___jp_782_:
{
if (v___y_784_ == 0)
{
lean_dec(v___x_781_);
v___y_674_ = v___y_783_;
v___y_675_ = v___y_785_;
v___y_676_ = v___y_786_;
v___y_677_ = v___y_787_;
v___y_678_ = v___y_788_;
v___y_679_ = v___y_789_;
goto v___jp_673_;
}
else
{
uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = 0;
lean_inc_ref(v_type_550_);
v___x_791_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_791_, 0, v_type_550_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*1, v___x_790_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*1 + 1, v_defeq_556_);
v___x_792_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_781_, v___x_791_);
lean_dec_ref_known(v___x_791_, 1);
lean_dec(v___x_781_);
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
v___x_799_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_549_, v_snd_798_);
lean_dec(v_snd_798_);
if (v___x_799_ == 0)
{
lean_dec(v_fst_797_);
lean_del_object(v___x_795_);
v___y_674_ = v___y_783_;
v___y_675_ = v___y_785_;
v___y_676_ = v___y_786_;
v___y_677_ = v___y_787_;
v___y_678_ = v___y_788_;
v___y_679_ = v___y_789_;
goto v___jp_673_;
}
else
{
lean_object* v___x_801_; 
lean_dec(v___y_785_);
lean_dec_ref(v___y_783_);
lean_dec_ref(v_env_563_);
lean_dec_ref(v_value_551_);
lean_dec_ref(v_type_550_);
lean_dec(v_levelParams_549_);
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
v___y_674_ = v___y_783_;
v___y_675_ = v___y_785_;
v___y_676_ = v___y_786_;
v___y_677_ = v___y_787_;
v___y_678_ = v___y_788_;
v___y_679_ = v___y_789_;
goto v___jp_673_;
}
}
}
v___jp_804_:
{
if (v_cache_553_ == 0)
{
lean_object* v___x_808_; lean_object* v_a_809_; lean_object* v___f_810_; uint8_t v___x_811_; 
lean_dec(v___x_781_);
v___x_808_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_807_, v_a_560_);
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc_n(v_a_809_, 2);
lean_dec_ref(v___x_808_);
lean_inc(v_levelParams_549_);
v___f_810_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_810_, 0, v_a_809_);
lean_closure_set(v___f_810_, 1, v_levelParams_549_);
lean_closure_set(v___f_810_, 2, v___y_805_);
lean_inc_ref(v_env_563_);
v___x_811_ = l_Lean_Environment_hasUnsafe(v_env_563_, v_type_550_);
if (v___x_811_ == 0)
{
uint8_t v___x_812_; 
v___x_812_ = l_Lean_Environment_hasUnsafe(v_env_563_, v_value_551_);
v___y_766_ = v___f_810_;
v___y_767_ = v_a_809_;
v___y_768_ = v___x_812_;
goto v___jp_765_;
}
else
{
lean_dec_ref(v_env_563_);
v___y_766_ = v___f_810_;
v___y_767_ = v_a_809_;
v___y_768_ = v___x_811_;
goto v___jp_765_;
}
}
else
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_781_, v___y_805_);
if (lean_obj_tag(v___x_813_) == 1)
{
lean_object* v_val_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_824_; 
v_val_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_824_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_824_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_val_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_824_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_fst_818_; lean_object* v_snd_819_; uint8_t v___x_820_; 
v_fst_818_ = lean_ctor_get(v_val_814_, 0);
lean_inc(v_fst_818_);
v_snd_819_ = lean_ctor_get(v_val_814_, 1);
lean_inc(v_snd_819_);
lean_dec(v_val_814_);
v___x_820_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_549_, v_snd_819_);
lean_dec(v_snd_819_);
if (v___x_820_ == 0)
{
lean_dec(v_fst_818_);
lean_del_object(v___x_816_);
v___y_783_ = v___y_805_;
v___y_784_ = v___y_806_;
v___y_785_ = v___y_807_;
v___y_786_ = v_a_557_;
v___y_787_ = v_a_558_;
v___y_788_ = v_a_559_;
v___y_789_ = v_a_560_;
goto v___jp_782_;
}
else
{
lean_object* v___x_822_; 
lean_dec(v___y_807_);
lean_dec_ref(v___y_805_);
lean_dec(v___x_781_);
lean_dec_ref(v_env_563_);
lean_dec_ref(v_value_551_);
lean_dec_ref(v_type_550_);
lean_dec(v_levelParams_549_);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 0);
lean_ctor_set(v___x_816_, 0, v_fst_818_);
v___x_822_ = v___x_816_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_fst_818_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_dec(v___x_813_);
v___y_783_ = v___y_805_;
v___y_784_ = v___y_806_;
v___y_785_ = v___y_807_;
v___y_786_ = v_a_557_;
v___y_787_ = v_a_558_;
v___y_788_ = v_a_559_;
v___y_789_ = v_a_560_;
goto v___jp_782_;
}
}
}
v___jp_825_:
{
lean_object* v___x_827_; 
lean_inc_ref(v_type_550_);
v___x_827_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_827_, 0, v_type_550_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*1, v___y_826_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*1 + 1, v_defeq_556_);
if (lean_obj_tag(v_kind_x3f_552_) == 0)
{
lean_object* v___x_828_; 
v___x_828_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__1));
v___y_805_ = v___x_827_;
v___y_806_ = v___y_826_;
v___y_807_ = v___x_828_;
goto v___jp_804_;
}
else
{
lean_object* v_val_829_; 
v_val_829_ = lean_ctor_get(v_kind_x3f_552_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v_kind_x3f_552_, 1);
v___y_805_ = v___x_827_;
v___y_806_ = v___y_826_;
v___y_807_ = v_val_829_;
goto v___jp_804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_832_, lean_object* v_type_833_, lean_object* v_value_834_, lean_object* v_kind_x3f_835_, lean_object* v_cache_836_, lean_object* v_inferRfl_837_, lean_object* v_forceExpose_838_, lean_object* v_defeq_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
uint8_t v_cache_boxed_845_; uint8_t v_inferRfl_boxed_846_; uint8_t v_forceExpose_boxed_847_; uint8_t v_defeq_boxed_848_; lean_object* v_res_849_; 
v_cache_boxed_845_ = lean_unbox(v_cache_836_);
v_inferRfl_boxed_846_ = lean_unbox(v_inferRfl_837_);
v_forceExpose_boxed_847_ = lean_unbox(v_forceExpose_838_);
v_defeq_boxed_848_ = lean_unbox(v_defeq_839_);
v_res_849_ = l_Lean_Meta_mkAuxLemma(v_levelParams_832_, v_type_833_, v_value_834_, v_kind_x3f_835_, v_cache_boxed_845_, v_inferRfl_boxed_846_, v_forceExpose_boxed_847_, v_defeq_boxed_848_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_851_, v_x_852_, v_x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(v_00_u03b2_859_, v_x_860_, v_x_861_);
lean_dec_ref(v_x_861_);
lean_dec_ref(v_x_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, size_t v_x_865_, size_t v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_864_, v_x_865_, v_x_866_, v_x_867_, v_x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
size_t v_x_6476__boxed_876_; size_t v_x_6477__boxed_877_; lean_object* v_res_878_; 
v_x_6476__boxed_876_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_x_6477__boxed_877_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_res_878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_870_, v_x_871_, v_x_6476__boxed_876_, v_x_6477__boxed_877_, v_x_874_, v_x_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b1_879_, lean_object* v_attrName_880_, lean_object* v_declName_881_, lean_object* v_asyncPrefix_x3f_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_880_, v_declName_881_, v_asyncPrefix_x3f_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_889_, lean_object* v_attrName_890_, lean_object* v_declName_891_, lean_object* v_asyncPrefix_x3f_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b1_889_, v_attrName_890_, v_declName_891_, v_asyncPrefix_x3f_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(lean_object* v_00_u03b1_899_, lean_object* v_attrName_900_, lean_object* v_declName_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_900_, v_declName_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___boxed(lean_object* v_00_u03b1_908_, lean_object* v_attrName_909_, lean_object* v_declName_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(v_00_u03b1_908_, v_attrName_909_, v_declName_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object* v_00_u03b2_917_, lean_object* v_x_918_, size_t v_x_919_, lean_object* v_x_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_918_, v_x_919_, v_x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object* v_00_u03b2_922_, lean_object* v_x_923_, lean_object* v_x_924_, lean_object* v_x_925_){
_start:
{
size_t v_x_6527__boxed_926_; lean_object* v_res_927_; 
v_x_6527__boxed_926_ = lean_unbox_usize(v_x_924_);
lean_dec(v_x_924_);
v_res_927_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(v_00_u03b2_922_, v_x_923_, v_x_6527__boxed_926_, v_x_925_);
lean_dec_ref(v_x_925_);
lean_dec_ref(v_x_923_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_928_, lean_object* v_n_929_, lean_object* v_k_930_, lean_object* v_v_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_929_, v_k_930_, v_v_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_933_, size_t v_depth_934_, lean_object* v_keys_935_, lean_object* v_vals_936_, lean_object* v_heq_937_, lean_object* v_i_938_, lean_object* v_entries_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_934_, v_keys_935_, v_vals_936_, v_i_938_, v_entries_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_941_, lean_object* v_depth_942_, lean_object* v_keys_943_, lean_object* v_vals_944_, lean_object* v_heq_945_, lean_object* v_i_946_, lean_object* v_entries_947_){
_start:
{
size_t v_depth_boxed_948_; lean_object* v_res_949_; 
v_depth_boxed_948_ = lean_unbox_usize(v_depth_942_);
lean_dec(v_depth_942_);
v_res_949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_941_, v_depth_boxed_948_, v_keys_943_, v_vals_944_, v_heq_945_, v_i_946_, v_entries_947_);
lean_dec_ref(v_vals_944_);
lean_dec_ref(v_keys_943_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_950_, lean_object* v_msg_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_958_, lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b1_958_, v_msg_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_966_, lean_object* v_keys_967_, lean_object* v_vals_968_, lean_object* v_heq_969_, lean_object* v_i_970_, lean_object* v_k_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_967_, v_vals_968_, v_i_970_, v_k_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_973_, lean_object* v_keys_974_, lean_object* v_vals_975_, lean_object* v_heq_976_, lean_object* v_i_977_, lean_object* v_k_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(v_00_u03b2_973_, v_keys_974_, v_vals_975_, v_heq_976_, v_i_977_, v_k_978_);
lean_dec_ref(v_k_978_);
lean_dec_ref(v_vals_975_);
lean_dec_ref(v_keys_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_x_981_, v_x_982_, v_x_983_, v_x_984_);
return v___x_985_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_DefEqAttrib(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
