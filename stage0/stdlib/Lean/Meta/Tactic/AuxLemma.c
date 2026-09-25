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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
v___x_39_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_62_; lean_object* v_auxDeclNGen_63_; lean_object* v___x_64_; lean_object* v_env_65_; lean_object* v___x_66_; lean_object* v_fst_67_; lean_object* v_snd_68_; lean_object* v___x_69_; lean_object* v_env_70_; lean_object* v_nextMacroScope_71_; lean_object* v_ngen_72_; lean_object* v_traceState_73_; lean_object* v_cache_74_; lean_object* v_recordedDeps_75_; lean_object* v_messages_76_; lean_object* v_infoState_77_; lean_object* v_snapshotTasks_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_87_; 
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
v_recordedDeps_75_ = lean_ctor_get(v___x_69_, 6);
v_messages_76_ = lean_ctor_get(v___x_69_, 7);
v_infoState_77_ = lean_ctor_get(v___x_69_, 8);
v_snapshotTasks_78_ = lean_ctor_get(v___x_69_, 9);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v___x_69_, 3);
lean_dec(v_unused_88_);
v___x_80_ = v___x_69_;
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_snapshotTasks_78_);
lean_inc(v_infoState_77_);
lean_inc(v_messages_76_);
lean_inc(v_recordedDeps_75_);
lean_inc(v_cache_74_);
lean_inc(v_traceState_73_);
lean_inc(v_ngen_72_);
lean_inc(v_nextMacroScope_71_);
lean_inc(v_env_70_);
lean_dec(v___x_69_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 3, v_snd_68_);
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_env_70_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_nextMacroScope_71_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_ngen_72_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v_snd_68_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v_traceState_73_);
lean_ctor_set(v_reuseFailAlloc_86_, 5, v_cache_74_);
lean_ctor_set(v_reuseFailAlloc_86_, 6, v_recordedDeps_75_);
lean_ctor_set(v_reuseFailAlloc_86_, 7, v_messages_76_);
lean_ctor_set(v_reuseFailAlloc_86_, 8, v_infoState_77_);
lean_ctor_set(v_reuseFailAlloc_86_, 9, v_snapshotTasks_78_);
v___x_83_ = v_reuseFailAlloc_86_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_st_ref_put(v___y_60_, v___x_83_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v_fst_67_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg___boxed(lean_object* v_kind_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_89_, v___y_90_);
lean_dec(v___y_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(lean_object* v_kind_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_93_, v___y_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___boxed(lean_object* v_kind_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(v_kind_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_ks_111_; lean_object* v_vs_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_136_; 
v_ks_111_ = lean_ctor_get(v_x_107_, 0);
v_vs_112_ = lean_ctor_get(v_x_107_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_x_107_);
if (v_isSharedCheck_136_ == 0)
{
v___x_114_ = v_x_107_;
v_isShared_115_ = v_isSharedCheck_136_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_vs_112_);
lean_inc(v_ks_111_);
lean_dec(v_x_107_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_136_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_array_get_size(v_ks_111_);
v___x_117_ = lean_nat_dec_lt(v_x_108_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
lean_dec(v_x_108_);
v___x_118_ = lean_array_push(v_ks_111_, v_x_109_);
v___x_119_ = lean_array_push(v_vs_112_, v_x_110_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___x_119_);
lean_ctor_set(v___x_114_, 0, v___x_118_);
v___x_121_ = v___x_114_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
else
{
lean_object* v_k_x27_123_; uint8_t v___x_124_; 
v_k_x27_123_ = lean_array_fget_borrowed(v_ks_111_, v_x_108_);
v___x_124_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_109_, v_k_x27_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_126_; 
if (v_isShared_115_ == 0)
{
v___x_126_ = v___x_114_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_ks_111_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_vs_112_);
v___x_126_ = v_reuseFailAlloc_130_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_add(v_x_108_, v___x_127_);
lean_dec(v_x_108_);
v_x_107_ = v___x_126_;
v_x_108_ = v___x_128_;
goto _start;
}
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_131_ = lean_array_fset(v_ks_111_, v_x_108_, v_x_109_);
v___x_132_ = lean_array_fset(v_vs_112_, v_x_108_, v_x_110_);
lean_dec(v_x_108_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___x_132_);
lean_ctor_set(v___x_114_, 0, v___x_131_);
v___x_134_ = v___x_114_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(lean_object* v_n_137_, lean_object* v_k_138_, lean_object* v_v_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_n_137_, v___x_140_, v_k_138_, v_v_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object* v_x_143_, size_t v_x_144_, size_t v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
lean_object* v_es_148_; size_t v___x_149_; size_t v___x_150_; lean_object* v_j_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v_es_148_ = lean_ctor_get(v_x_143_, 0);
v___x_149_ = ((size_t)31ULL);
v___x_150_ = lean_usize_land(v_x_144_, v___x_149_);
v_j_151_ = lean_usize_to_nat(v___x_150_);
v___x_152_ = lean_array_get_size(v_es_148_);
v___x_153_ = lean_nat_dec_lt(v_j_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_dec(v_j_151_);
lean_dec(v_x_147_);
lean_dec_ref(v_x_146_);
return v_x_143_;
}
else
{
lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_192_; 
lean_inc_ref(v_es_148_);
v_isSharedCheck_192_ = !lean_is_exclusive(v_x_143_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v_x_143_, 0);
lean_dec(v_unused_193_);
v___x_155_ = v_x_143_;
v_isShared_156_ = v_isSharedCheck_192_;
goto v_resetjp_154_;
}
else
{
lean_dec(v_x_143_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_192_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_v_157_; lean_object* v___x_158_; lean_object* v_xs_x27_159_; lean_object* v___y_161_; 
v_v_157_ = lean_array_fget(v_es_148_, v_j_151_);
v___x_158_ = lean_box(0);
v_xs_x27_159_ = lean_array_fset(v_es_148_, v_j_151_, v___x_158_);
switch(lean_obj_tag(v_v_157_))
{
case 0:
{
lean_object* v_key_166_; lean_object* v_val_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_177_; 
v_key_166_ = lean_ctor_get(v_v_157_, 0);
v_val_167_ = lean_ctor_get(v_v_157_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_v_157_);
if (v_isSharedCheck_177_ == 0)
{
v___x_169_ = v_v_157_;
v_isShared_170_ = v_isSharedCheck_177_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_val_167_);
lean_inc(v_key_166_);
lean_dec(v_v_157_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_177_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
uint8_t v___x_171_; 
v___x_171_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_146_, v_key_166_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_del_object(v___x_169_);
v___x_172_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_166_, v_val_167_, v_x_146_, v_x_147_);
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
v___y_161_ = v___x_173_;
goto v___jp_160_;
}
else
{
lean_object* v___x_175_; 
lean_dec(v_val_167_);
lean_dec(v_key_166_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 1, v_x_147_);
lean_ctor_set(v___x_169_, 0, v_x_146_);
v___x_175_ = v___x_169_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_x_146_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_x_147_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
v___y_161_ = v___x_175_;
goto v___jp_160_;
}
}
}
}
case 1:
{
lean_object* v_node_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_190_; 
v_node_178_ = lean_ctor_get(v_v_157_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v_v_157_);
if (v_isSharedCheck_190_ == 0)
{
v___x_180_ = v_v_157_;
v_isShared_181_ = v_isSharedCheck_190_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_node_178_);
lean_dec(v_v_157_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_190_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; size_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_182_ = ((size_t)5ULL);
v___x_183_ = lean_usize_shift_right(v_x_144_, v___x_182_);
v___x_184_ = ((size_t)1ULL);
v___x_185_ = lean_usize_add(v_x_145_, v___x_184_);
v___x_186_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_node_178_, v___x_183_, v___x_185_, v_x_146_, v_x_147_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_186_);
v___x_188_ = v___x_180_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
v___y_161_ = v___x_188_;
goto v___jp_160_;
}
}
}
default: 
{
lean_object* v___x_191_; 
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v_x_146_);
lean_ctor_set(v___x_191_, 1, v_x_147_);
v___y_161_ = v___x_191_;
goto v___jp_160_;
}
}
v___jp_160_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_array_fset(v_xs_x27_159_, v_j_151_, v___y_161_);
lean_dec(v_j_151_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_162_);
v___x_164_ = v___x_155_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
else
{
lean_object* v_ks_194_; lean_object* v_vs_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_213_; 
v_ks_194_ = lean_ctor_get(v_x_143_, 0);
v_vs_195_ = lean_ctor_get(v_x_143_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_143_);
if (v_isSharedCheck_213_ == 0)
{
v___x_197_ = v_x_143_;
v_isShared_198_ = v_isSharedCheck_213_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_vs_195_);
lean_inc(v_ks_194_);
lean_dec(v_x_143_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_213_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_ks_194_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_vs_195_);
v___x_200_ = v_reuseFailAlloc_212_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v_newNode_201_; size_t v___x_202_; uint8_t v___x_203_; 
v_newNode_201_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v___x_200_, v_x_146_, v_x_147_);
v___x_202_ = ((size_t)7ULL);
v___x_203_ = lean_usize_dec_le(v___x_202_, v_x_145_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_201_);
v___x_205_ = lean_unsigned_to_nat(4u);
v___x_206_ = lean_nat_dec_lt(v___x_204_, v___x_205_);
lean_dec(v___x_204_);
if (v___x_206_ == 0)
{
lean_object* v_ks_207_; lean_object* v_vs_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_ks_207_ = lean_ctor_get(v_newNode_201_, 0);
lean_inc_ref(v_ks_207_);
v_vs_208_ = lean_ctor_get(v_newNode_201_, 1);
lean_inc_ref(v_vs_208_);
lean_dec_ref(v_newNode_201_);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0);
v___x_211_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_x_145_, v_ks_207_, v_vs_208_, v___x_209_, v___x_210_);
lean_dec_ref(v_vs_208_);
lean_dec_ref(v_ks_207_);
return v___x_211_;
}
else
{
return v_newNode_201_;
}
}
else
{
return v_newNode_201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t v_depth_214_, lean_object* v_keys_215_, lean_object* v_vals_216_, lean_object* v_i_217_, lean_object* v_entries_218_){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_array_get_size(v_keys_215_);
v___x_220_ = lean_nat_dec_lt(v_i_217_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec(v_i_217_);
return v_entries_218_;
}
else
{
lean_object* v_k_221_; lean_object* v_v_222_; uint64_t v___x_223_; size_t v_h_224_; size_t v___x_225_; lean_object* v___x_226_; size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; size_t v_h_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_k_221_ = lean_array_fget_borrowed(v_keys_215_, v_i_217_);
v_v_222_ = lean_array_fget_borrowed(v_vals_216_, v_i_217_);
v___x_223_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_k_221_);
v_h_224_ = lean_uint64_to_usize(v___x_223_);
v___x_225_ = ((size_t)5ULL);
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = ((size_t)1ULL);
v___x_228_ = lean_usize_sub(v_depth_214_, v___x_227_);
v___x_229_ = lean_usize_mul(v___x_225_, v___x_228_);
v_h_230_ = lean_usize_shift_right(v_h_224_, v___x_229_);
v___x_231_ = lean_nat_add(v_i_217_, v___x_226_);
lean_dec(v_i_217_);
lean_inc(v_v_222_);
lean_inc(v_k_221_);
v___x_232_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_entries_218_, v_h_230_, v_depth_214_, v_k_221_, v_v_222_);
v_i_217_ = v___x_231_;
v_entries_218_ = v___x_232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_234_, lean_object* v_keys_235_, lean_object* v_vals_236_, lean_object* v_i_237_, lean_object* v_entries_238_){
_start:
{
size_t v_depth_boxed_239_; lean_object* v_res_240_; 
v_depth_boxed_239_ = lean_unbox_usize(v_depth_234_);
lean_dec(v_depth_234_);
v_res_240_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_boxed_239_, v_keys_235_, v_vals_236_, v_i_237_, v_entries_238_);
lean_dec_ref(v_vals_236_);
lean_dec_ref(v_keys_235_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
size_t v_x_5366__boxed_246_; size_t v_x_5367__boxed_247_; lean_object* v_res_248_; 
v_x_5366__boxed_246_ = lean_unbox_usize(v_x_242_);
lean_dec(v_x_242_);
v_x_5367__boxed_247_ = lean_unbox_usize(v_x_243_);
lean_dec(v_x_243_);
v_res_248_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_241_, v_x_5366__boxed_246_, v_x_5367__boxed_247_, v_x_244_, v_x_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
uint64_t v___x_252_; size_t v___x_253_; size_t v___x_254_; lean_object* v___x_255_; 
v___x_252_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_250_);
v___x_253_ = lean_uint64_to_usize(v___x_252_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_249_, v___x_253_, v___x_254_, v_x_250_, v_x_251_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object* v_a_256_, lean_object* v_levelParams_257_, lean_object* v___x_258_, lean_object* v_x_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v_a_256_);
lean_ctor_set(v___x_260_, 1, v_levelParams_257_);
v___x_261_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_259_, v___x_258_, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(lean_object* v_msgData_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; lean_object* v_env_269_; lean_object* v___x_270_; lean_object* v_toCold_271_; lean_object* v_mctx_272_; lean_object* v_lctx_273_; lean_object* v_options_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_268_ = lean_st_ref_get(v___y_266_);
v_env_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_ref(v_env_269_);
lean_dec(v___x_268_);
v___x_270_ = lean_st_ref_get(v___y_264_);
v_toCold_271_ = lean_ctor_get(v___y_265_, 0);
v_mctx_272_ = lean_ctor_get(v___x_270_, 0);
lean_inc_ref(v_mctx_272_);
lean_dec(v___x_270_);
v_lctx_273_ = lean_ctor_get(v___y_263_, 2);
v_options_274_ = lean_ctor_get(v_toCold_271_, 2);
lean_inc_ref(v_options_274_);
lean_inc_ref(v_lctx_273_);
v___x_275_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_275_, 0, v_env_269_);
lean_ctor_set(v___x_275_, 1, v_mctx_272_);
lean_ctor_set(v___x_275_, 2, v_lctx_273_);
lean_ctor_set(v___x_275_, 3, v_options_274_);
v___x_276_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v_msgData_262_);
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
v_ref_291_ = lean_ctor_get(v___y_288_, 2);
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
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
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
lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___x_448_; lean_object* v_env_449_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___x_464_; 
v___x_448_ = lean_st_ref_get(v___y_402_);
v_env_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_env_449_);
lean_dec(v___x_448_);
v___x_464_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_449_, v_decl_398_);
if (lean_obj_tag(v___x_464_) == 0)
{
v___y_451_ = v___y_399_;
v___y_452_ = v___y_400_;
v___y_453_ = v___y_401_;
v___y_454_ = v___y_402_;
goto v___jp_450_;
}
else
{
lean_object* v_attr_465_; lean_object* v_toAttributeImplCore_466_; lean_object* v_name_467_; lean_object* v___x_468_; 
lean_dec_ref_known(v___x_464_, 1);
lean_dec_ref(v_env_449_);
v_attr_465_ = lean_ctor_get(v_attr_397_, 0);
lean_inc_ref(v_attr_465_);
lean_dec_ref(v_attr_397_);
v_toAttributeImplCore_466_ = lean_ctor_get(v_attr_465_, 0);
lean_inc_ref(v_toAttributeImplCore_466_);
lean_dec_ref(v_attr_465_);
v_name_467_ = lean_ctor_get(v_toAttributeImplCore_466_, 1);
lean_inc(v_name_467_);
lean_dec_ref(v_toAttributeImplCore_466_);
v___x_468_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_name_467_, v_decl_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
return v___x_468_;
}
v___jp_404_:
{
lean_object* v___x_407_; lean_object* v_ext_408_; lean_object* v_toEnvExtension_409_; lean_object* v_env_410_; lean_object* v_nextMacroScope_411_; lean_object* v_ngen_412_; lean_object* v_auxDeclNGen_413_; lean_object* v_traceState_414_; lean_object* v_recordedDeps_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_446_; 
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
v_recordedDeps_415_ = lean_ctor_get(v___x_407_, 6);
v_messages_416_ = lean_ctor_get(v___x_407_, 7);
v_infoState_417_ = lean_ctor_get(v___x_407_, 8);
v_snapshotTasks_418_ = lean_ctor_get(v___x_407_, 9);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v___x_407_, 5);
lean_dec(v_unused_447_);
v___x_420_ = v___x_407_;
v_isShared_421_ = v_isSharedCheck_446_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_recordedDeps_415_);
lean_inc(v_traceState_414_);
lean_inc(v_auxDeclNGen_413_);
lean_inc(v_ngen_412_);
lean_inc(v_nextMacroScope_411_);
lean_inc(v_env_410_);
lean_dec(v___x_407_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_446_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_asyncMode_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v_asyncMode_422_ = lean_ctor_get(v_toEnvExtension_409_, 2);
lean_inc(v_asyncMode_422_);
lean_inc(v_decl_398_);
v___x_423_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_408_, v_env_410_, v_decl_398_, v_asyncMode_422_, v_decl_398_);
lean_dec(v_asyncMode_422_);
v___x_424_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
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
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_nextMacroScope_411_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_ngen_412_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_auxDeclNGen_413_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_traceState_414_);
lean_ctor_set(v_reuseFailAlloc_445_, 5, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_445_, 6, v_recordedDeps_415_);
lean_ctor_set(v_reuseFailAlloc_445_, 7, v_messages_416_);
lean_ctor_set(v_reuseFailAlloc_445_, 8, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_445_, 9, v_snapshotTasks_418_);
v___x_426_ = v_reuseFailAlloc_445_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_mctx_429_; lean_object* v_zetaDeltaFVarIds_430_; lean_object* v_postponed_431_; lean_object* v_diag_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_443_; 
v___x_427_ = lean_st_ref_put(v___y_406_, v___x_426_);
v___x_428_ = lean_st_ref_take(v___y_405_);
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
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = lean_box(0);
v___x_437_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_437_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_mctx_429_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_zetaDeltaFVarIds_430_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_postponed_431_);
lean_ctor_set(v_reuseFailAlloc_442_, 4, v_diag_432_);
v___x_439_ = v_reuseFailAlloc_442_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_st_ref_put(v___y_405_, v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_436_);
return v___x_441_;
}
}
}
}
}
v___jp_450_:
{
lean_object* v_ext_455_; lean_object* v_toEnvExtension_456_; lean_object* v_attr_457_; lean_object* v_asyncMode_458_; uint8_t v___x_459_; 
v_ext_455_ = lean_ctor_get(v_attr_397_, 1);
v_toEnvExtension_456_ = lean_ctor_get(v_ext_455_, 0);
v_attr_457_ = lean_ctor_get(v_attr_397_, 0);
v_asyncMode_458_ = lean_ctor_get(v_toEnvExtension_456_, 2);
lean_inc(v_decl_398_);
lean_inc_ref(v_env_449_);
v___x_459_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_449_, v_decl_398_, v_asyncMode_458_);
if (v___x_459_ == 0)
{
lean_object* v_toAttributeImplCore_460_; lean_object* v_name_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc_ref(v_attr_457_);
lean_dec_ref(v_attr_397_);
v_toAttributeImplCore_460_ = lean_ctor_get(v_attr_457_, 0);
lean_inc_ref(v_toAttributeImplCore_460_);
lean_dec_ref(v_attr_457_);
v_name_461_ = lean_ctor_get(v_toAttributeImplCore_460_, 1);
lean_inc(v_name_461_);
lean_dec_ref(v_toAttributeImplCore_460_);
v___x_462_ = l_Lean_Environment_asyncPrefix_x3f(v_env_449_);
v___x_463_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_name_461_, v_decl_398_, v___x_462_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
return v___x_463_;
}
else
{
lean_dec_ref(v_env_449_);
v___y_405_ = v___y_452_;
v___y_406_ = v___y_454_;
goto v___jp_404_;
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
size_t v_x_5903__boxed_522_; lean_object* v_res_523_; 
v_x_5903__boxed_522_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_res_523_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_519_, v_x_5903__boxed_522_, v_x_521_);
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
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_env_565_; lean_object* v___x_566_; lean_object* v_asyncMode_567_; uint8_t v_isExporting_568_; lean_object* v___x_569_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; uint8_t v___y_662_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_769_; lean_object* v___y_770_; uint8_t v___y_771_; lean_object* v___x_784_; lean_object* v___y_786_; lean_object* v___y_787_; uint8_t v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_808_; uint8_t v___y_809_; lean_object* v___y_810_; uint8_t v___y_829_; 
v___x_563_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_564_ = lean_st_ref_get(v_a_561_);
v_env_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref_n(v_env_565_, 2);
lean_dec(v___x_564_);
v___x_566_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_567_ = lean_ctor_get(v___x_566_, 2);
v_isExporting_568_ = lean_ctor_get_uint8(v_env_565_, sizeof(void*)*8);
v___x_569_ = lean_box(0);
v___x_784_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_563_, v___x_566_, v_env_565_, v_asyncMode_567_, v___x_569_);
if (v_isExporting_568_ == 0)
{
uint8_t v___x_833_; 
v___x_833_ = 1;
v___y_829_ = v___x_833_;
goto v___jp_828_;
}
else
{
uint8_t v___x_834_; 
v___x_834_ = 0;
v___y_829_ = v___x_834_;
goto v___jp_828_;
}
v___jp_570_:
{
lean_object* v___x_575_; lean_object* v_env_576_; lean_object* v_nextMacroScope_577_; lean_object* v_ngen_578_; lean_object* v_auxDeclNGen_579_; lean_object* v_traceState_580_; lean_object* v_recordedDeps_581_; lean_object* v_messages_582_; lean_object* v_infoState_583_; lean_object* v_snapshotTasks_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_610_; 
v___x_575_ = lean_st_ref_take(v___y_574_);
v_env_576_ = lean_ctor_get(v___x_575_, 0);
v_nextMacroScope_577_ = lean_ctor_get(v___x_575_, 1);
v_ngen_578_ = lean_ctor_get(v___x_575_, 2);
v_auxDeclNGen_579_ = lean_ctor_get(v___x_575_, 3);
v_traceState_580_ = lean_ctor_get(v___x_575_, 4);
v_recordedDeps_581_ = lean_ctor_get(v___x_575_, 6);
v_messages_582_ = lean_ctor_get(v___x_575_, 7);
v_infoState_583_ = lean_ctor_get(v___x_575_, 8);
v_snapshotTasks_584_ = lean_ctor_get(v___x_575_, 9);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_575_, 5);
lean_dec(v_unused_611_);
v___x_586_ = v___x_575_;
v_isShared_587_ = v_isSharedCheck_610_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_snapshotTasks_584_);
lean_inc(v_infoState_583_);
lean_inc(v_messages_582_);
lean_inc(v_recordedDeps_581_);
lean_inc(v_traceState_580_);
lean_inc(v_auxDeclNGen_579_);
lean_inc(v_ngen_578_);
lean_inc(v_nextMacroScope_577_);
lean_inc(v_env_576_);
lean_dec(v___x_575_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_610_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_588_ = l_Lean_EnvExtension_modifyState___redArg(v___x_566_, v_env_576_, v___y_571_, v_asyncMode_567_, v___x_569_);
v___x_589_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 5, v___x_589_);
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_591_ = v___x_586_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_nextMacroScope_577_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_ngen_578_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_auxDeclNGen_579_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_traceState_580_);
lean_ctor_set(v_reuseFailAlloc_609_, 5, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_609_, 6, v_recordedDeps_581_);
lean_ctor_set(v_reuseFailAlloc_609_, 7, v_messages_582_);
lean_ctor_set(v_reuseFailAlloc_609_, 8, v_infoState_583_);
lean_ctor_set(v_reuseFailAlloc_609_, 9, v_snapshotTasks_584_);
v___x_591_ = v_reuseFailAlloc_609_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_mctx_594_; lean_object* v_zetaDeltaFVarIds_595_; lean_object* v_postponed_596_; lean_object* v_diag_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_607_; 
v___x_592_ = lean_st_ref_put(v___y_574_, v___x_591_);
v___x_593_ = lean_st_ref_take(v___y_573_);
v_mctx_594_ = lean_ctor_get(v___x_593_, 0);
v_zetaDeltaFVarIds_595_ = lean_ctor_get(v___x_593_, 2);
v_postponed_596_ = lean_ctor_get(v___x_593_, 3);
v_diag_597_ = lean_ctor_get(v___x_593_, 4);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v___x_593_, 1);
lean_dec(v_unused_608_);
v___x_599_ = v___x_593_;
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_diag_597_);
lean_inc(v_postponed_596_);
lean_inc(v_zetaDeltaFVarIds_595_);
lean_inc(v_mctx_594_);
lean_dec(v___x_593_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_mctx_594_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_zetaDeltaFVarIds_595_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v_postponed_596_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v_diag_597_);
v___x_603_ = v_reuseFailAlloc_606_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_st_ref_put(v___y_573_, v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___y_572_);
return v___x_605_;
}
}
}
}
}
v___jp_612_:
{
if (v_inferRfl_555_ == 0)
{
v___y_571_ = v___y_613_;
v___y_572_ = v___y_614_;
v___y_573_ = v___y_616_;
v___y_574_ = v___y_618_;
goto v___jp_570_;
}
else
{
lean_object* v___x_619_; 
lean_inc(v___y_614_);
v___x_619_ = l_Lean_inferDefEqAttr(v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_dec_ref_known(v___x_619_, 1);
v___y_571_ = v___y_613_;
v___y_572_ = v___y_614_;
v___y_573_ = v___y_616_;
v___y_574_ = v___y_618_;
goto v___jp_570_;
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
v___jp_628_:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_addDecl(v___y_635_, v_forceExpose_556_, v___y_632_, v___y_630_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_dec_ref_known(v___x_636_, 1);
if (v_defeq_557_ == 0)
{
v___y_613_ = v___y_633_;
v___y_614_ = v___y_634_;
v___y_615_ = v___y_631_;
v___y_616_ = v___y_629_;
v___y_617_ = v___y_632_;
v___y_618_ = v___y_630_;
goto v___jp_612_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = l_Lean_defeqAttr;
lean_inc(v___y_634_);
v___x_638_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_637_, v___y_634_, v___y_631_, v___y_629_, v___y_632_, v___y_630_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_dec_ref_known(v___x_638_, 1);
v___y_613_ = v___y_633_;
v___y_614_ = v___y_634_;
v___y_615_ = v___y_631_;
v___y_616_ = v___y_629_;
v___y_617_ = v___y_632_;
v___y_618_ = v___y_630_;
goto v___jp_612_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
v_a_647_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_636_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_636_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
v___jp_655_:
{
if (v___y_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_inc_n(v___y_661_, 2);
v___x_663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_663_, 0, v___y_661_);
lean_ctor_set(v___x_663_, 1, v_levelParams_550_);
lean_ctor_set(v___x_663_, 2, v_type_551_);
v___x_664_ = lean_box(0);
v___x_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_665_, 0, v___y_661_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_666_, 0, v___x_663_);
lean_ctor_set(v___x_666_, 1, v_value_552_);
lean_ctor_set(v___x_666_, 2, v___x_665_);
v___x_667_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
v___y_629_ = v___y_656_;
v___y_630_ = v___y_657_;
v___y_631_ = v___y_658_;
v___y_632_ = v___y_659_;
v___y_633_ = v___y_660_;
v___y_634_ = v___y_661_;
v___y_635_ = v___x_667_;
goto v___jp_628_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_inc_n(v___y_661_, 2);
v___x_668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_668_, 0, v___y_661_);
lean_ctor_set(v___x_668_, 1, v_levelParams_550_);
lean_ctor_set(v___x_668_, 2, v_type_551_);
v___x_669_ = lean_box(0);
v___x_670_ = 0;
v___x_671_ = lean_box(0);
v___x_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_672_, 0, v___y_661_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_673_, 0, v___x_668_);
lean_ctor_set(v___x_673_, 1, v_value_552_);
lean_ctor_set(v___x_673_, 2, v___x_669_);
lean_ctor_set(v___x_673_, 3, v___x_672_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*4, v___x_670_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
v___y_629_ = v___y_656_;
v___y_630_ = v___y_657_;
v___y_631_ = v___y_658_;
v___y_632_ = v___y_659_;
v___y_633_ = v___y_660_;
v___y_634_ = v___y_661_;
v___y_635_ = v___x_674_;
goto v___jp_628_;
}
}
v___jp_675_:
{
lean_object* v___x_682_; lean_object* v_a_683_; lean_object* v___f_684_; uint8_t v___x_685_; 
v___x_682_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_677_, v___y_681_);
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc_n(v_a_683_, 2);
lean_dec_ref(v___x_682_);
lean_inc(v_levelParams_550_);
v___f_684_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_684_, 0, v_a_683_);
lean_closure_set(v___f_684_, 1, v_levelParams_550_);
lean_closure_set(v___f_684_, 2, v___y_676_);
lean_inc_ref(v_env_565_);
v___x_685_ = l_Lean_Environment_hasUnsafe(v_env_565_, v_type_551_);
if (v___x_685_ == 0)
{
uint8_t v___x_686_; 
v___x_686_ = l_Lean_Environment_hasUnsafe(v_env_565_, v_value_552_);
v___y_656_ = v___y_679_;
v___y_657_ = v___y_681_;
v___y_658_ = v___y_678_;
v___y_659_ = v___y_680_;
v___y_660_ = v___f_684_;
v___y_661_ = v_a_683_;
v___y_662_ = v___x_686_;
goto v___jp_655_;
}
else
{
lean_dec_ref(v_env_565_);
v___y_656_ = v___y_679_;
v___y_657_ = v___y_681_;
v___y_658_ = v___y_678_;
v___y_659_ = v___y_680_;
v___y_660_ = v___f_684_;
v___y_661_ = v_a_683_;
v___y_662_ = v___x_685_;
goto v___jp_655_;
}
}
v___jp_687_:
{
lean_object* v___x_692_; lean_object* v_env_693_; lean_object* v_nextMacroScope_694_; lean_object* v_ngen_695_; lean_object* v_auxDeclNGen_696_; lean_object* v_traceState_697_; lean_object* v_recordedDeps_698_; lean_object* v_messages_699_; lean_object* v_infoState_700_; lean_object* v_snapshotTasks_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_727_; 
v___x_692_ = lean_st_ref_take(v___y_691_);
v_env_693_ = lean_ctor_get(v___x_692_, 0);
v_nextMacroScope_694_ = lean_ctor_get(v___x_692_, 1);
v_ngen_695_ = lean_ctor_get(v___x_692_, 2);
v_auxDeclNGen_696_ = lean_ctor_get(v___x_692_, 3);
v_traceState_697_ = lean_ctor_get(v___x_692_, 4);
v_recordedDeps_698_ = lean_ctor_get(v___x_692_, 6);
v_messages_699_ = lean_ctor_get(v___x_692_, 7);
v_infoState_700_ = lean_ctor_get(v___x_692_, 8);
v_snapshotTasks_701_ = lean_ctor_get(v___x_692_, 9);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v___x_692_, 5);
lean_dec(v_unused_728_);
v___x_703_ = v___x_692_;
v_isShared_704_ = v_isSharedCheck_727_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_snapshotTasks_701_);
lean_inc(v_infoState_700_);
lean_inc(v_messages_699_);
lean_inc(v_recordedDeps_698_);
lean_inc(v_traceState_697_);
lean_inc(v_auxDeclNGen_696_);
lean_inc(v_ngen_695_);
lean_inc(v_nextMacroScope_694_);
lean_inc(v_env_693_);
lean_dec(v___x_692_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_727_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_705_ = l_Lean_EnvExtension_modifyState___redArg(v___x_566_, v_env_693_, v___y_688_, v_asyncMode_567_, v___x_569_);
v___x_706_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 5, v___x_706_);
lean_ctor_set(v___x_703_, 0, v___x_705_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_nextMacroScope_694_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_ngen_695_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_auxDeclNGen_696_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_traceState_697_);
lean_ctor_set(v_reuseFailAlloc_726_, 5, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_726_, 6, v_recordedDeps_698_);
lean_ctor_set(v_reuseFailAlloc_726_, 7, v_messages_699_);
lean_ctor_set(v_reuseFailAlloc_726_, 8, v_infoState_700_);
lean_ctor_set(v_reuseFailAlloc_726_, 9, v_snapshotTasks_701_);
v___x_708_ = v_reuseFailAlloc_726_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_mctx_711_; lean_object* v_zetaDeltaFVarIds_712_; lean_object* v_postponed_713_; lean_object* v_diag_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_724_; 
v___x_709_ = lean_st_ref_put(v___y_691_, v___x_708_);
v___x_710_ = lean_st_ref_take(v___y_690_);
v_mctx_711_ = lean_ctor_get(v___x_710_, 0);
v_zetaDeltaFVarIds_712_ = lean_ctor_get(v___x_710_, 2);
v_postponed_713_ = lean_ctor_get(v___x_710_, 3);
v_diag_714_ = lean_ctor_get(v___x_710_, 4);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_710_, 1);
lean_dec(v_unused_725_);
v___x_716_ = v___x_710_;
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_diag_714_);
lean_inc(v_postponed_713_);
lean_inc(v_zetaDeltaFVarIds_712_);
lean_inc(v_mctx_711_);
lean_dec(v___x_710_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_mctx_711_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_zetaDeltaFVarIds_712_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_postponed_713_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_diag_714_);
v___x_720_ = v_reuseFailAlloc_723_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_st_ref_put(v___y_690_, v___x_720_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___y_689_);
return v___x_722_;
}
}
}
}
}
v___jp_729_:
{
if (v_inferRfl_555_ == 0)
{
v___y_688_ = v___y_730_;
v___y_689_ = v___y_731_;
v___y_690_ = v___y_733_;
v___y_691_ = v___y_735_;
goto v___jp_687_;
}
else
{
lean_object* v___x_736_; 
lean_inc(v___y_731_);
v___x_736_ = l_Lean_inferDefEqAttr(v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_dec_ref_known(v___x_736_, 1);
v___y_688_ = v___y_730_;
v___y_689_ = v___y_731_;
v___y_690_ = v___y_733_;
v___y_691_ = v___y_735_;
goto v___jp_687_;
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
v___jp_745_:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_addDecl(v___y_748_, v_forceExpose_556_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_dec_ref_known(v___x_749_, 1);
if (v_defeq_557_ == 0)
{
v___y_730_ = v___y_746_;
v___y_731_ = v___y_747_;
v___y_732_ = v_a_558_;
v___y_733_ = v_a_559_;
v___y_734_ = v_a_560_;
v___y_735_ = v_a_561_;
goto v___jp_729_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = l_Lean_defeqAttr;
lean_inc(v___y_747_);
v___x_751_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_750_, v___y_747_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_dec_ref_known(v___x_751_, 1);
v___y_730_ = v___y_746_;
v___y_731_ = v___y_747_;
v___y_732_ = v_a_558_;
v___y_733_ = v_a_559_;
v___y_734_ = v_a_560_;
v___y_735_ = v_a_561_;
goto v___jp_729_;
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
v_a_760_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_749_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_749_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
v___jp_768_:
{
if (v___y_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_inc_n(v___y_770_, 2);
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v___y_770_);
lean_ctor_set(v___x_772_, 1, v_levelParams_550_);
lean_ctor_set(v___x_772_, 2, v_type_551_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_774_, 0, v___y_770_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_775_, 0, v___x_772_);
lean_ctor_set(v___x_775_, 1, v_value_552_);
lean_ctor_set(v___x_775_, 2, v___x_774_);
v___x_776_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
v___y_746_ = v___y_769_;
v___y_747_ = v___y_770_;
v___y_748_ = v___x_776_;
goto v___jp_745_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_inc_n(v___y_770_, 2);
v___x_777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_777_, 0, v___y_770_);
lean_ctor_set(v___x_777_, 1, v_levelParams_550_);
lean_ctor_set(v___x_777_, 2, v_type_551_);
v___x_778_ = lean_box(0);
v___x_779_ = 0;
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_781_, 0, v___y_770_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_782_, 0, v___x_777_);
lean_ctor_set(v___x_782_, 1, v_value_552_);
lean_ctor_set(v___x_782_, 2, v___x_778_);
lean_ctor_set(v___x_782_, 3, v___x_781_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*4, v___x_779_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
v___y_746_ = v___y_769_;
v___y_747_ = v___y_770_;
v___y_748_ = v___x_783_;
goto v___jp_745_;
}
}
v___jp_785_:
{
if (v___y_788_ == 0)
{
lean_dec(v___x_784_);
v___y_676_ = v___y_786_;
v___y_677_ = v___y_787_;
v___y_678_ = v___y_789_;
v___y_679_ = v___y_790_;
v___y_680_ = v___y_791_;
v___y_681_ = v___y_792_;
goto v___jp_675_;
}
else
{
uint8_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_793_ = 0;
lean_inc_ref(v_type_551_);
v___x_794_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_794_, 0, v_type_551_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*1, v___x_793_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*1 + 1, v_defeq_557_);
v___x_795_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_784_, v___x_794_);
lean_dec_ref_known(v___x_794_, 1);
lean_dec(v___x_784_);
if (lean_obj_tag(v___x_795_) == 1)
{
lean_object* v_val_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_806_; 
v_val_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_806_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_val_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_fst_800_; lean_object* v_snd_801_; uint8_t v___x_802_; 
v_fst_800_ = lean_ctor_get(v_val_796_, 0);
lean_inc(v_fst_800_);
v_snd_801_ = lean_ctor_get(v_val_796_, 1);
lean_inc(v_snd_801_);
lean_dec(v_val_796_);
v___x_802_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_550_, v_snd_801_);
lean_dec(v_snd_801_);
if (v___x_802_ == 0)
{
lean_dec(v_fst_800_);
lean_del_object(v___x_798_);
v___y_676_ = v___y_786_;
v___y_677_ = v___y_787_;
v___y_678_ = v___y_789_;
v___y_679_ = v___y_790_;
v___y_680_ = v___y_791_;
v___y_681_ = v___y_792_;
goto v___jp_675_;
}
else
{
lean_object* v___x_804_; 
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec_ref(v_env_565_);
lean_dec_ref(v_value_552_);
lean_dec_ref(v_type_551_);
lean_dec(v_levelParams_550_);
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 0);
lean_ctor_set(v___x_798_, 0, v_fst_800_);
v___x_804_ = v___x_798_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_fst_800_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_dec(v___x_795_);
v___y_676_ = v___y_786_;
v___y_677_ = v___y_787_;
v___y_678_ = v___y_789_;
v___y_679_ = v___y_790_;
v___y_680_ = v___y_791_;
v___y_681_ = v___y_792_;
goto v___jp_675_;
}
}
}
v___jp_807_:
{
if (v_cache_554_ == 0)
{
lean_object* v___x_811_; lean_object* v_a_812_; lean_object* v___f_813_; uint8_t v___x_814_; 
lean_dec(v___x_784_);
v___x_811_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_810_, v_a_561_);
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc_n(v_a_812_, 2);
lean_dec_ref(v___x_811_);
lean_inc(v_levelParams_550_);
v___f_813_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_813_, 0, v_a_812_);
lean_closure_set(v___f_813_, 1, v_levelParams_550_);
lean_closure_set(v___f_813_, 2, v___y_808_);
lean_inc_ref(v_env_565_);
v___x_814_ = l_Lean_Environment_hasUnsafe(v_env_565_, v_type_551_);
if (v___x_814_ == 0)
{
uint8_t v___x_815_; 
v___x_815_ = l_Lean_Environment_hasUnsafe(v_env_565_, v_value_552_);
v___y_769_ = v___f_813_;
v___y_770_ = v_a_812_;
v___y_771_ = v___x_815_;
goto v___jp_768_;
}
else
{
lean_dec_ref(v_env_565_);
v___y_769_ = v___f_813_;
v___y_770_ = v_a_812_;
v___y_771_ = v___x_814_;
goto v___jp_768_;
}
}
else
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_784_, v___y_808_);
if (lean_obj_tag(v___x_816_) == 1)
{
lean_object* v_val_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_827_; 
v_val_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_827_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_827_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_val_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_827_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_fst_821_; lean_object* v_snd_822_; uint8_t v___x_823_; 
v_fst_821_ = lean_ctor_get(v_val_817_, 0);
lean_inc(v_fst_821_);
v_snd_822_ = lean_ctor_get(v_val_817_, 1);
lean_inc(v_snd_822_);
lean_dec(v_val_817_);
v___x_823_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_550_, v_snd_822_);
lean_dec(v_snd_822_);
if (v___x_823_ == 0)
{
lean_dec(v_fst_821_);
lean_del_object(v___x_819_);
v___y_786_ = v___y_808_;
v___y_787_ = v___y_810_;
v___y_788_ = v___y_809_;
v___y_789_ = v_a_558_;
v___y_790_ = v_a_559_;
v___y_791_ = v_a_560_;
v___y_792_ = v_a_561_;
goto v___jp_785_;
}
else
{
lean_object* v___x_825_; 
lean_dec(v___y_810_);
lean_dec_ref(v___y_808_);
lean_dec(v___x_784_);
lean_dec_ref(v_env_565_);
lean_dec_ref(v_value_552_);
lean_dec_ref(v_type_551_);
lean_dec(v_levelParams_550_);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 0);
lean_ctor_set(v___x_819_, 0, v_fst_821_);
v___x_825_ = v___x_819_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_fst_821_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
lean_dec(v___x_816_);
v___y_786_ = v___y_808_;
v___y_787_ = v___y_810_;
v___y_788_ = v___y_809_;
v___y_789_ = v_a_558_;
v___y_790_ = v_a_559_;
v___y_791_ = v_a_560_;
v___y_792_ = v_a_561_;
goto v___jp_785_;
}
}
}
v___jp_828_:
{
lean_object* v___x_830_; 
lean_inc_ref(v_type_551_);
v___x_830_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_830_, 0, v_type_551_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*1, v___y_829_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*1 + 1, v_defeq_557_);
if (lean_obj_tag(v_kind_x3f_553_) == 0)
{
lean_object* v___x_831_; 
v___x_831_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__1));
v___y_808_ = v___x_830_;
v___y_809_ = v___y_829_;
v___y_810_ = v___x_831_;
goto v___jp_807_;
}
else
{
lean_object* v_val_832_; 
v_val_832_ = lean_ctor_get(v_kind_x3f_553_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v_kind_x3f_553_, 1);
v___y_808_ = v___x_830_;
v___y_809_ = v___y_829_;
v___y_810_ = v_val_832_;
goto v___jp_807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_835_, lean_object* v_type_836_, lean_object* v_value_837_, lean_object* v_kind_x3f_838_, lean_object* v_cache_839_, lean_object* v_inferRfl_840_, lean_object* v_forceExpose_841_, lean_object* v_defeq_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
uint8_t v_cache_boxed_848_; uint8_t v_inferRfl_boxed_849_; uint8_t v_forceExpose_boxed_850_; uint8_t v_defeq_boxed_851_; lean_object* v_res_852_; 
v_cache_boxed_848_ = lean_unbox(v_cache_839_);
v_inferRfl_boxed_849_ = lean_unbox(v_inferRfl_840_);
v_forceExpose_boxed_850_ = lean_unbox(v_forceExpose_841_);
v_defeq_boxed_851_ = lean_unbox(v_defeq_842_);
v_res_852_ = l_Lean_Meta_mkAuxLemma(v_levelParams_835_, v_type_836_, v_value_837_, v_kind_x3f_838_, v_cache_boxed_848_, v_inferRfl_boxed_849_, v_forceExpose_boxed_850_, v_defeq_boxed_851_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_853_, lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v_x_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_854_, v_x_855_, v_x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_00_u03b2_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(v_00_u03b2_862_, v_x_863_, v_x_864_);
lean_dec_ref(v_x_864_);
lean_dec_ref(v_x_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, size_t v_x_868_, size_t v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_867_, v_x_868_, v_x_869_, v_x_870_, v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
size_t v_x_6538__boxed_879_; size_t v_x_6539__boxed_880_; lean_object* v_res_881_; 
v_x_6538__boxed_879_ = lean_unbox_usize(v_x_875_);
lean_dec(v_x_875_);
v_x_6539__boxed_880_ = lean_unbox_usize(v_x_876_);
lean_dec(v_x_876_);
v_res_881_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_873_, v_x_874_, v_x_6538__boxed_879_, v_x_6539__boxed_880_, v_x_877_, v_x_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b1_882_, lean_object* v_attrName_883_, lean_object* v_declName_884_, lean_object* v_asyncPrefix_x3f_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_883_, v_declName_884_, v_asyncPrefix_x3f_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_892_, lean_object* v_attrName_893_, lean_object* v_declName_894_, lean_object* v_asyncPrefix_x3f_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b1_892_, v_attrName_893_, v_declName_894_, v_asyncPrefix_x3f_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(lean_object* v_00_u03b1_902_, lean_object* v_attrName_903_, lean_object* v_declName_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_903_, v_declName_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___boxed(lean_object* v_00_u03b1_911_, lean_object* v_attrName_912_, lean_object* v_declName_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(v_00_u03b1_911_, v_attrName_912_, v_declName_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object* v_00_u03b2_920_, lean_object* v_x_921_, size_t v_x_922_, lean_object* v_x_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_921_, v_x_922_, v_x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object* v_00_u03b2_925_, lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
size_t v_x_6589__boxed_929_; lean_object* v_res_930_; 
v_x_6589__boxed_929_ = lean_unbox_usize(v_x_927_);
lean_dec(v_x_927_);
v_res_930_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(v_00_u03b2_925_, v_x_926_, v_x_6589__boxed_929_, v_x_928_);
lean_dec_ref(v_x_928_);
lean_dec_ref(v_x_926_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_931_, lean_object* v_n_932_, lean_object* v_k_933_, lean_object* v_v_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_932_, v_k_933_, v_v_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_936_, size_t v_depth_937_, lean_object* v_keys_938_, lean_object* v_vals_939_, lean_object* v_heq_940_, lean_object* v_i_941_, lean_object* v_entries_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_937_, v_keys_938_, v_vals_939_, v_i_941_, v_entries_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_944_, lean_object* v_depth_945_, lean_object* v_keys_946_, lean_object* v_vals_947_, lean_object* v_heq_948_, lean_object* v_i_949_, lean_object* v_entries_950_){
_start:
{
size_t v_depth_boxed_951_; lean_object* v_res_952_; 
v_depth_boxed_951_ = lean_unbox_usize(v_depth_945_);
lean_dec(v_depth_945_);
v_res_952_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_944_, v_depth_boxed_951_, v_keys_946_, v_vals_947_, v_heq_948_, v_i_949_, v_entries_950_);
lean_dec_ref(v_vals_947_);
lean_dec_ref(v_keys_946_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_953_, lean_object* v_msg_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_961_, lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b1_961_, v_msg_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_969_, lean_object* v_keys_970_, lean_object* v_vals_971_, lean_object* v_heq_972_, lean_object* v_i_973_, lean_object* v_k_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_970_, v_vals_971_, v_i_973_, v_k_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_976_, lean_object* v_keys_977_, lean_object* v_vals_978_, lean_object* v_heq_979_, lean_object* v_i_980_, lean_object* v_k_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(v_00_u03b2_976_, v_keys_977_, v_vals_978_, v_heq_979_, v_i_980_, v_k_981_);
lean_dec_ref(v_k_981_);
lean_dec_ref(v_vals_978_);
lean_dec_ref(v_keys_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_x_984_, v_x_985_, v_x_986_, v_x_987_);
return v___x_988_;
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
