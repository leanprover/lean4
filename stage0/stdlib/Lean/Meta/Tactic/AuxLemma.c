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
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; 
v___f_53_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_box(1);
v___x_56_ = lean_box(0);
v___x_57_ = 0;
v___x_58_ = l_Lean_registerEnvExtension___redArg(v___f_53_, v___x_54_, v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(lean_object* v_kind_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; lean_object* v_auxDeclNGen_65_; lean_object* v___x_66_; lean_object* v_env_67_; lean_object* v___x_68_; lean_object* v_fst_69_; lean_object* v_snd_70_; lean_object* v___x_71_; lean_object* v_env_72_; lean_object* v_nextMacroScope_73_; lean_object* v_ngen_74_; lean_object* v_traceState_75_; lean_object* v_cache_76_; lean_object* v_recordedDeps_77_; lean_object* v_messages_78_; lean_object* v_infoState_79_; lean_object* v_snapshotTasks_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_89_; 
v___x_64_ = lean_st_ref_get(v___y_62_);
v_auxDeclNGen_65_ = lean_ctor_get(v___x_64_, 3);
lean_inc_ref(v_auxDeclNGen_65_);
lean_dec(v___x_64_);
v___x_66_ = lean_st_ref_get(v___y_62_);
v_env_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc_ref(v_env_67_);
lean_dec(v___x_66_);
v___x_68_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_67_, v_auxDeclNGen_65_, v_kind_61_);
v_fst_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_fst_69_);
v_snd_70_ = lean_ctor_get(v___x_68_, 1);
lean_inc(v_snd_70_);
lean_dec_ref(v___x_68_);
v___x_71_ = lean_st_ref_take(v___y_62_);
v_env_72_ = lean_ctor_get(v___x_71_, 0);
v_nextMacroScope_73_ = lean_ctor_get(v___x_71_, 1);
v_ngen_74_ = lean_ctor_get(v___x_71_, 2);
v_traceState_75_ = lean_ctor_get(v___x_71_, 4);
v_cache_76_ = lean_ctor_get(v___x_71_, 5);
v_recordedDeps_77_ = lean_ctor_get(v___x_71_, 6);
v_messages_78_ = lean_ctor_get(v___x_71_, 7);
v_infoState_79_ = lean_ctor_get(v___x_71_, 8);
v_snapshotTasks_80_ = lean_ctor_get(v___x_71_, 9);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v___x_71_, 3);
lean_dec(v_unused_90_);
v___x_82_ = v___x_71_;
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_snapshotTasks_80_);
lean_inc(v_infoState_79_);
lean_inc(v_messages_78_);
lean_inc(v_recordedDeps_77_);
lean_inc(v_cache_76_);
lean_inc(v_traceState_75_);
lean_inc(v_ngen_74_);
lean_inc(v_nextMacroScope_73_);
lean_inc(v_env_72_);
lean_dec(v___x_71_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 3, v_snd_70_);
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_env_72_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_nextMacroScope_73_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v_ngen_74_);
lean_ctor_set(v_reuseFailAlloc_88_, 3, v_snd_70_);
lean_ctor_set(v_reuseFailAlloc_88_, 4, v_traceState_75_);
lean_ctor_set(v_reuseFailAlloc_88_, 5, v_cache_76_);
lean_ctor_set(v_reuseFailAlloc_88_, 6, v_recordedDeps_77_);
lean_ctor_set(v_reuseFailAlloc_88_, 7, v_messages_78_);
lean_ctor_set(v_reuseFailAlloc_88_, 8, v_infoState_79_);
lean_ctor_set(v_reuseFailAlloc_88_, 9, v_snapshotTasks_80_);
v___x_85_ = v_reuseFailAlloc_88_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_st_ref_put(v___y_62_, v___x_85_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v_fst_69_);
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg___boxed(lean_object* v_kind_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_91_, v___y_92_);
lean_dec(v___y_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(lean_object* v_kind_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_95_, v___y_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___boxed(lean_object* v_kind_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(v_kind_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
lean_object* v_ks_113_; lean_object* v_vs_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_138_; 
v_ks_113_ = lean_ctor_get(v_x_109_, 0);
v_vs_114_ = lean_ctor_get(v_x_109_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_109_);
if (v_isSharedCheck_138_ == 0)
{
v___x_116_ = v_x_109_;
v_isShared_117_ = v_isSharedCheck_138_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_vs_114_);
lean_inc(v_ks_113_);
lean_dec(v_x_109_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_138_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_array_get_size(v_ks_113_);
v___x_119_ = lean_nat_dec_lt(v_x_110_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
lean_dec(v_x_110_);
v___x_120_ = lean_array_push(v_ks_113_, v_x_111_);
v___x_121_ = lean_array_push(v_vs_114_, v_x_112_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v___x_121_);
lean_ctor_set(v___x_116_, 0, v___x_120_);
v___x_123_ = v___x_116_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
else
{
lean_object* v_k_x27_125_; uint8_t v___x_126_; 
v_k_x27_125_ = lean_array_fget_borrowed(v_ks_113_, v_x_110_);
v___x_126_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_111_, v_k_x27_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_128_; 
if (v_isShared_117_ == 0)
{
v___x_128_ = v___x_116_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_ks_113_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_vs_114_);
v___x_128_ = v_reuseFailAlloc_132_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_add(v_x_110_, v___x_129_);
lean_dec(v_x_110_);
v_x_109_ = v___x_128_;
v_x_110_ = v___x_130_;
goto _start;
}
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = lean_array_fset(v_ks_113_, v_x_110_, v_x_111_);
v___x_134_ = lean_array_fset(v_vs_114_, v_x_110_, v_x_112_);
lean_dec(v_x_110_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v___x_134_);
lean_ctor_set(v___x_116_, 0, v___x_133_);
v___x_136_ = v___x_116_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(lean_object* v_n_139_, lean_object* v_k_140_, lean_object* v_v_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_n_139_, v___x_142_, v_k_140_, v_v_141_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object* v_x_145_, size_t v_x_146_, size_t v_x_147_, lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v_es_150_; size_t v___x_151_; size_t v___x_152_; lean_object* v_j_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_es_150_ = lean_ctor_get(v_x_145_, 0);
v___x_151_ = ((size_t)31ULL);
v___x_152_ = lean_usize_land(v_x_146_, v___x_151_);
v_j_153_ = lean_usize_to_nat(v___x_152_);
v___x_154_ = lean_array_get_size(v_es_150_);
v___x_155_ = lean_nat_dec_lt(v_j_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_dec(v_j_153_);
lean_dec(v_x_149_);
lean_dec_ref(v_x_148_);
return v_x_145_;
}
else
{
lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_194_; 
lean_inc_ref(v_es_150_);
v_isSharedCheck_194_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v_x_145_, 0);
lean_dec(v_unused_195_);
v___x_157_ = v_x_145_;
v_isShared_158_ = v_isSharedCheck_194_;
goto v_resetjp_156_;
}
else
{
lean_dec(v_x_145_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_194_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v_v_159_; lean_object* v___x_160_; lean_object* v_xs_x27_161_; lean_object* v___y_163_; 
v_v_159_ = lean_array_fget(v_es_150_, v_j_153_);
v___x_160_ = lean_box(0);
v_xs_x27_161_ = lean_array_fset(v_es_150_, v_j_153_, v___x_160_);
switch(lean_obj_tag(v_v_159_))
{
case 0:
{
lean_object* v_key_168_; lean_object* v_val_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_179_; 
v_key_168_ = lean_ctor_get(v_v_159_, 0);
v_val_169_ = lean_ctor_get(v_v_159_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_v_159_);
if (v_isSharedCheck_179_ == 0)
{
v___x_171_ = v_v_159_;
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_val_169_);
lean_inc(v_key_168_);
lean_dec(v_v_159_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
uint8_t v___x_173_; 
v___x_173_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_148_, v_key_168_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_del_object(v___x_171_);
v___x_174_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_168_, v_val_169_, v_x_148_, v_x_149_);
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
v___y_163_ = v___x_175_;
goto v___jp_162_;
}
else
{
lean_object* v___x_177_; 
lean_dec(v_val_169_);
lean_dec(v_key_168_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v_x_149_);
lean_ctor_set(v___x_171_, 0, v_x_148_);
v___x_177_ = v___x_171_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_x_148_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_x_149_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
v___y_163_ = v___x_177_;
goto v___jp_162_;
}
}
}
}
case 1:
{
lean_object* v_node_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_192_; 
v_node_180_ = lean_ctor_get(v_v_159_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v_v_159_);
if (v_isSharedCheck_192_ == 0)
{
v___x_182_ = v_v_159_;
v_isShared_183_ = v_isSharedCheck_192_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_node_180_);
lean_dec(v_v_159_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_192_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
size_t v___x_184_; size_t v___x_185_; size_t v___x_186_; size_t v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_184_ = ((size_t)5ULL);
v___x_185_ = lean_usize_shift_right(v_x_146_, v___x_184_);
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_add(v_x_147_, v___x_186_);
v___x_188_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_node_180_, v___x_185_, v___x_187_, v_x_148_, v_x_149_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_188_);
v___x_190_ = v___x_182_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
v___y_163_ = v___x_190_;
goto v___jp_162_;
}
}
}
default: 
{
lean_object* v___x_193_; 
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v_x_148_);
lean_ctor_set(v___x_193_, 1, v_x_149_);
v___y_163_ = v___x_193_;
goto v___jp_162_;
}
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = lean_array_fset(v_xs_x27_161_, v_j_153_, v___y_163_);
lean_dec(v_j_153_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_164_);
v___x_166_ = v___x_157_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
else
{
lean_object* v_ks_196_; lean_object* v_vs_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_215_; 
v_ks_196_ = lean_ctor_get(v_x_145_, 0);
v_vs_197_ = lean_ctor_get(v_x_145_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_215_ == 0)
{
v___x_199_ = v_x_145_;
v_isShared_200_ = v_isSharedCheck_215_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_vs_197_);
lean_inc(v_ks_196_);
lean_dec(v_x_145_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_215_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_ks_196_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_vs_197_);
v___x_202_ = v_reuseFailAlloc_214_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v_newNode_203_; size_t v___x_204_; uint8_t v___x_205_; 
v_newNode_203_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v___x_202_, v_x_148_, v_x_149_);
v___x_204_ = ((size_t)7ULL);
v___x_205_ = lean_usize_dec_le(v___x_204_, v_x_147_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_203_);
v___x_207_ = lean_unsigned_to_nat(4u);
v___x_208_ = lean_nat_dec_lt(v___x_206_, v___x_207_);
lean_dec(v___x_206_);
if (v___x_208_ == 0)
{
lean_object* v_ks_209_; lean_object* v_vs_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_ks_209_ = lean_ctor_get(v_newNode_203_, 0);
lean_inc_ref(v_ks_209_);
v_vs_210_ = lean_ctor_get(v_newNode_203_, 1);
lean_inc_ref(v_vs_210_);
lean_dec_ref(v_newNode_203_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0);
v___x_213_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_x_147_, v_ks_209_, v_vs_210_, v___x_211_, v___x_212_);
lean_dec_ref(v_vs_210_);
lean_dec_ref(v_ks_209_);
return v___x_213_;
}
else
{
return v_newNode_203_;
}
}
else
{
return v_newNode_203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t v_depth_216_, lean_object* v_keys_217_, lean_object* v_vals_218_, lean_object* v_i_219_, lean_object* v_entries_220_){
_start:
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_array_get_size(v_keys_217_);
v___x_222_ = lean_nat_dec_lt(v_i_219_, v___x_221_);
if (v___x_222_ == 0)
{
lean_dec(v_i_219_);
return v_entries_220_;
}
else
{
lean_object* v_k_223_; lean_object* v_v_224_; uint64_t v___x_225_; size_t v_h_226_; size_t v___x_227_; lean_object* v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; size_t v_h_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_k_223_ = lean_array_fget_borrowed(v_keys_217_, v_i_219_);
v_v_224_ = lean_array_fget_borrowed(v_vals_218_, v_i_219_);
v___x_225_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_k_223_);
v_h_226_ = lean_uint64_to_usize(v___x_225_);
v___x_227_ = ((size_t)5ULL);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_sub(v_depth_216_, v___x_229_);
v___x_231_ = lean_usize_mul(v___x_227_, v___x_230_);
v_h_232_ = lean_usize_shift_right(v_h_226_, v___x_231_);
v___x_233_ = lean_nat_add(v_i_219_, v___x_228_);
lean_dec(v_i_219_);
lean_inc(v_v_224_);
lean_inc(v_k_223_);
v___x_234_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_entries_220_, v_h_232_, v_depth_216_, v_k_223_, v_v_224_);
v_i_219_ = v___x_233_;
v_entries_220_ = v___x_234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_236_, lean_object* v_keys_237_, lean_object* v_vals_238_, lean_object* v_i_239_, lean_object* v_entries_240_){
_start:
{
size_t v_depth_boxed_241_; lean_object* v_res_242_; 
v_depth_boxed_241_ = lean_unbox_usize(v_depth_236_);
lean_dec(v_depth_236_);
v_res_242_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_boxed_241_, v_keys_237_, v_vals_238_, v_i_239_, v_entries_240_);
lean_dec_ref(v_vals_238_);
lean_dec_ref(v_keys_237_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
size_t v_x_5377__boxed_248_; size_t v_x_5378__boxed_249_; lean_object* v_res_250_; 
v_x_5377__boxed_248_ = lean_unbox_usize(v_x_244_);
lean_dec(v_x_244_);
v_x_5378__boxed_249_ = lean_unbox_usize(v_x_245_);
lean_dec(v_x_245_);
v_res_250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_243_, v_x_5377__boxed_248_, v_x_5378__boxed_249_, v_x_246_, v_x_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
uint64_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; 
v___x_254_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_252_);
v___x_255_ = lean_uint64_to_usize(v___x_254_);
v___x_256_ = ((size_t)1ULL);
v___x_257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_251_, v___x_255_, v___x_256_, v_x_252_, v_x_253_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object* v_a_258_, lean_object* v_levelParams_259_, lean_object* v___x_260_, lean_object* v_x_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_a_258_);
lean_ctor_set(v___x_262_, 1, v_levelParams_259_);
v___x_263_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_261_, v___x_260_, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(lean_object* v_msgData_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; lean_object* v_env_271_; lean_object* v___x_272_; lean_object* v_toCold_273_; lean_object* v_mctx_274_; lean_object* v_lctx_275_; lean_object* v_options_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_270_ = lean_st_ref_get(v___y_268_);
v_env_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_ref(v_env_271_);
lean_dec(v___x_270_);
v___x_272_ = lean_st_ref_get(v___y_266_);
v_toCold_273_ = lean_ctor_get(v___y_267_, 0);
v_mctx_274_ = lean_ctor_get(v___x_272_, 0);
lean_inc_ref(v_mctx_274_);
lean_dec(v___x_272_);
v_lctx_275_ = lean_ctor_get(v___y_265_, 2);
v_options_276_ = lean_ctor_get(v_toCold_273_, 2);
lean_inc_ref(v_options_276_);
lean_inc_ref(v_lctx_275_);
v___x_277_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_277_, 0, v_env_271_);
lean_ctor_set(v___x_277_, 1, v_mctx_274_);
lean_ctor_set(v___x_277_, 2, v_lctx_275_);
lean_ctor_set(v___x_277_, 3, v_options_276_);
v___x_278_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_msgData_264_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_msgData_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msgData_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_ref_293_; lean_object* v___x_294_; lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v_ref_293_ = lean_ctor_get(v___y_290_, 2);
v___x_294_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msg_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_303_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
lean_inc(v_ref_293_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_ref_293_);
lean_ctor_set(v___x_299_, 1, v_a_295_);
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 1);
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_msg_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_310_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0));
v___x_313_ = l_Lean_stringToMessageData(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2));
v___x_316_ = l_Lean_stringToMessageData(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4));
v___x_319_ = l_Lean_stringToMessageData(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6));
v___x_322_ = l_Lean_stringToMessageData(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8));
v___x_325_ = l_Lean_stringToMessageData(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(lean_object* v_attrName_326_, lean_object* v_declName_327_, lean_object* v_asyncPrefix_x3f_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___y_335_; 
if (lean_obj_tag(v_asyncPrefix_x3f_328_) == 0)
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_MessageData_nil;
v___y_335_ = v___x_348_;
goto v___jp_334_;
}
else
{
lean_object* v_val_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_val_349_ = lean_ctor_get(v_asyncPrefix_x3f_328_, 0);
lean_inc(v_val_349_);
lean_dec_ref_known(v_asyncPrefix_x3f_328_, 1);
v___x_350_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7);
v___x_351_ = l_Lean_MessageData_ofName(v_val_349_);
v___x_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___y_335_ = v___x_354_;
goto v___jp_334_;
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_336_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_337_ = l_Lean_MessageData_ofName(v_attrName_326_);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = 0;
v___x_342_ = l_Lean_MessageData_ofConstName(v_declName_327_, v___x_341_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_340_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___y_335_);
v___x_347_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_346_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object* v_attrName_355_, lean_object* v_declName_356_, lean_object* v_asyncPrefix_x3f_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_355_, v_declName_356_, v_asyncPrefix_x3f_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_363_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(lean_object* v_attrName_367_, lean_object* v_declName_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_374_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_375_ = l_Lean_MessageData_ofName(v_attrName_367_);
v___x_376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = 0;
v___x_380_ = l_Lean_MessageData_ofConstName(v_declName_368_, v___x_379_);
v___x_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_378_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1);
v___x_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_383_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___boxed(lean_object* v_attrName_385_, lean_object* v_declName_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_385_, v_declName_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_392_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_398_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
lean_ctor_set(v___x_398_, 2, v___x_397_);
lean_ctor_set(v___x_398_, 3, v___x_397_);
lean_ctor_set(v___x_398_, 4, v___x_397_);
lean_ctor_set(v___x_398_, 5, v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object* v_attr_399_, lean_object* v_decl_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___x_450_; lean_object* v_env_451_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___x_466_; 
v___x_450_ = lean_st_ref_get(v___y_404_);
v_env_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_env_451_);
lean_dec(v___x_450_);
v___x_466_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_451_, v_decl_400_);
if (lean_obj_tag(v___x_466_) == 0)
{
v___y_453_ = v___y_401_;
v___y_454_ = v___y_402_;
v___y_455_ = v___y_403_;
v___y_456_ = v___y_404_;
goto v___jp_452_;
}
else
{
lean_object* v_attr_467_; lean_object* v_toAttributeImplCore_468_; lean_object* v_name_469_; lean_object* v___x_470_; 
lean_dec_ref_known(v___x_466_, 1);
lean_dec_ref(v_env_451_);
v_attr_467_ = lean_ctor_get(v_attr_399_, 0);
lean_inc_ref(v_attr_467_);
lean_dec_ref(v_attr_399_);
v_toAttributeImplCore_468_ = lean_ctor_get(v_attr_467_, 0);
lean_inc_ref(v_toAttributeImplCore_468_);
lean_dec_ref(v_attr_467_);
v_name_469_ = lean_ctor_get(v_toAttributeImplCore_468_, 1);
lean_inc(v_name_469_);
lean_dec_ref(v_toAttributeImplCore_468_);
v___x_470_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_name_469_, v_decl_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
return v___x_470_;
}
v___jp_406_:
{
lean_object* v___x_409_; lean_object* v_ext_410_; lean_object* v_toEnvExtension_411_; lean_object* v_env_412_; lean_object* v_nextMacroScope_413_; lean_object* v_ngen_414_; lean_object* v_auxDeclNGen_415_; lean_object* v_traceState_416_; lean_object* v_recordedDeps_417_; lean_object* v_messages_418_; lean_object* v_infoState_419_; lean_object* v_snapshotTasks_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_448_; 
v___x_409_ = lean_st_ref_take(v___y_408_);
v_ext_410_ = lean_ctor_get(v_attr_399_, 1);
lean_inc_ref(v_ext_410_);
lean_dec_ref(v_attr_399_);
v_toEnvExtension_411_ = lean_ctor_get(v_ext_410_, 0);
v_env_412_ = lean_ctor_get(v___x_409_, 0);
v_nextMacroScope_413_ = lean_ctor_get(v___x_409_, 1);
v_ngen_414_ = lean_ctor_get(v___x_409_, 2);
v_auxDeclNGen_415_ = lean_ctor_get(v___x_409_, 3);
v_traceState_416_ = lean_ctor_get(v___x_409_, 4);
v_recordedDeps_417_ = lean_ctor_get(v___x_409_, 6);
v_messages_418_ = lean_ctor_get(v___x_409_, 7);
v_infoState_419_ = lean_ctor_get(v___x_409_, 8);
v_snapshotTasks_420_ = lean_ctor_get(v___x_409_, 9);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v___x_409_, 5);
lean_dec(v_unused_449_);
v___x_422_ = v___x_409_;
v_isShared_423_ = v_isSharedCheck_448_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_snapshotTasks_420_);
lean_inc(v_infoState_419_);
lean_inc(v_messages_418_);
lean_inc(v_recordedDeps_417_);
lean_inc(v_traceState_416_);
lean_inc(v_auxDeclNGen_415_);
lean_inc(v_ngen_414_);
lean_inc(v_nextMacroScope_413_);
lean_inc(v_env_412_);
lean_dec(v___x_409_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_448_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_asyncMode_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v_asyncMode_424_ = lean_ctor_get(v_toEnvExtension_411_, 2);
lean_inc(v_asyncMode_424_);
lean_inc(v_decl_400_);
v___x_425_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_410_, v_env_412_, v_decl_400_, v_asyncMode_424_, v_decl_400_);
lean_dec(v_asyncMode_424_);
v___x_426_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 5, v___x_426_);
lean_ctor_set(v___x_422_, 0, v___x_425_);
v___x_428_ = v___x_422_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_nextMacroScope_413_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_ngen_414_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_auxDeclNGen_415_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_traceState_416_);
lean_ctor_set(v_reuseFailAlloc_447_, 5, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 6, v_recordedDeps_417_);
lean_ctor_set(v_reuseFailAlloc_447_, 7, v_messages_418_);
lean_ctor_set(v_reuseFailAlloc_447_, 8, v_infoState_419_);
lean_ctor_set(v_reuseFailAlloc_447_, 9, v_snapshotTasks_420_);
v___x_428_ = v_reuseFailAlloc_447_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v_mctx_431_; lean_object* v_zetaDeltaFVarIds_432_; lean_object* v_postponed_433_; lean_object* v_diag_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_445_; 
v___x_429_ = lean_st_ref_put(v___y_408_, v___x_428_);
v___x_430_ = lean_st_ref_take(v___y_407_);
v_mctx_431_ = lean_ctor_get(v___x_430_, 0);
v_zetaDeltaFVarIds_432_ = lean_ctor_get(v___x_430_, 2);
v_postponed_433_ = lean_ctor_get(v___x_430_, 3);
v_diag_434_ = lean_ctor_get(v___x_430_, 4);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_430_, 1);
lean_dec(v_unused_446_);
v___x_436_ = v___x_430_;
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_diag_434_);
lean_inc(v_postponed_433_);
lean_inc(v_zetaDeltaFVarIds_432_);
lean_inc(v_mctx_431_);
lean_dec(v___x_430_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = lean_box(0);
v___x_439_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_mctx_431_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_zetaDeltaFVarIds_432_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_postponed_433_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_diag_434_);
v___x_441_ = v_reuseFailAlloc_444_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_st_ref_put(v___y_407_, v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_438_);
return v___x_443_;
}
}
}
}
}
v___jp_452_:
{
lean_object* v_ext_457_; lean_object* v_toEnvExtension_458_; lean_object* v_attr_459_; lean_object* v_asyncMode_460_; uint8_t v___x_461_; 
v_ext_457_ = lean_ctor_get(v_attr_399_, 1);
v_toEnvExtension_458_ = lean_ctor_get(v_ext_457_, 0);
v_attr_459_ = lean_ctor_get(v_attr_399_, 0);
v_asyncMode_460_ = lean_ctor_get(v_toEnvExtension_458_, 2);
lean_inc(v_decl_400_);
lean_inc_ref(v_env_451_);
v___x_461_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_451_, v_decl_400_, v_asyncMode_460_);
if (v___x_461_ == 0)
{
lean_object* v_toAttributeImplCore_462_; lean_object* v_name_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_inc_ref(v_attr_459_);
lean_dec_ref(v_attr_399_);
v_toAttributeImplCore_462_ = lean_ctor_get(v_attr_459_, 0);
lean_inc_ref(v_toAttributeImplCore_462_);
lean_dec_ref(v_attr_459_);
v_name_463_ = lean_ctor_get(v_toAttributeImplCore_462_, 1);
lean_inc(v_name_463_);
lean_dec_ref(v_toAttributeImplCore_462_);
v___x_464_ = l_Lean_Environment_asyncPrefix_x3f(v_env_451_);
v___x_465_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_name_463_, v_decl_400_, v___x_464_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v___x_465_;
}
else
{
lean_dec_ref(v_env_451_);
v___y_407_ = v___y_454_;
v___y_408_ = v___y_456_;
goto v___jp_406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object* v_attr_471_, lean_object* v_decl_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v_attr_471_, v_decl_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(lean_object* v_keys_479_, lean_object* v_vals_480_, lean_object* v_i_481_, lean_object* v_k_482_){
_start:
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_array_get_size(v_keys_479_);
v___x_484_ = lean_nat_dec_lt(v_i_481_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
lean_dec(v_i_481_);
v___x_485_ = lean_box(0);
return v___x_485_;
}
else
{
lean_object* v_k_x27_486_; uint8_t v___x_487_; 
v_k_x27_486_ = lean_array_fget_borrowed(v_keys_479_, v_i_481_);
v___x_487_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_k_482_, v_k_x27_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_i_481_, v___x_488_);
lean_dec(v_i_481_);
v_i_481_ = v___x_489_;
goto _start;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_array_fget_borrowed(v_vals_480_, v_i_481_);
lean_dec(v_i_481_);
lean_inc(v___x_491_);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_i_495_, lean_object* v_k_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_493_, v_vals_494_, v_i_495_, v_k_496_);
lean_dec_ref(v_k_496_);
lean_dec_ref(v_vals_494_);
lean_dec_ref(v_keys_493_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(lean_object* v_x_498_, size_t v_x_499_, lean_object* v_x_500_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v_es_501_; lean_object* v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v_j_505_; lean_object* v___x_506_; 
v_es_501_ = lean_ctor_get(v_x_498_, 0);
v___x_502_ = lean_box(2);
v___x_503_ = ((size_t)31ULL);
v___x_504_ = lean_usize_land(v_x_499_, v___x_503_);
v_j_505_ = lean_usize_to_nat(v___x_504_);
v___x_506_ = lean_array_get_borrowed(v___x_502_, v_es_501_, v_j_505_);
lean_dec(v_j_505_);
switch(lean_obj_tag(v___x_506_))
{
case 0:
{
lean_object* v_key_507_; lean_object* v_val_508_; uint8_t v___x_509_; 
v_key_507_ = lean_ctor_get(v___x_506_, 0);
v_val_508_ = lean_ctor_get(v___x_506_, 1);
v___x_509_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_500_, v_key_507_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
v___x_510_ = lean_box(0);
return v___x_510_;
}
else
{
lean_object* v___x_511_; 
lean_inc(v_val_508_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v_val_508_);
return v___x_511_;
}
}
case 1:
{
lean_object* v_node_512_; size_t v___x_513_; size_t v___x_514_; 
v_node_512_ = lean_ctor_get(v___x_506_, 0);
v___x_513_ = ((size_t)5ULL);
v___x_514_ = lean_usize_shift_right(v_x_499_, v___x_513_);
v_x_498_ = v_node_512_;
v_x_499_ = v___x_514_;
goto _start;
}
default: 
{
lean_object* v___x_516_; 
v___x_516_ = lean_box(0);
return v___x_516_;
}
}
}
else
{
lean_object* v_ks_517_; lean_object* v_vs_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_ks_517_ = lean_ctor_get(v_x_498_, 0);
v_vs_518_ = lean_ctor_get(v_x_498_, 1);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_ks_517_, v_vs_518_, v___x_519_, v_x_500_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
size_t v_x_5914__boxed_524_; lean_object* v_res_525_; 
v_x_5914__boxed_524_ = lean_unbox_usize(v_x_522_);
lean_dec(v_x_522_);
v_res_525_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_521_, v_x_5914__boxed_524_, v_x_523_);
lean_dec_ref(v_x_523_);
lean_dec_ref(v_x_521_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
uint64_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; 
v___x_528_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_527_);
v___x_529_ = lean_uint64_to_usize(v___x_528_);
v___x_530_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_526_, v___x_529_, v_x_527_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg___boxed(lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_531_, v_x_532_);
lean_dec_ref(v_x_532_);
lean_dec_ref(v_x_531_);
return v_res_533_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
if (lean_obj_tag(v_x_535_) == 0)
{
uint8_t v___x_536_; 
v___x_536_ = 1;
return v___x_536_;
}
else
{
uint8_t v___x_537_; 
v___x_537_ = 0;
return v___x_537_;
}
}
else
{
if (lean_obj_tag(v_x_535_) == 0)
{
uint8_t v___x_538_; 
v___x_538_ = 0;
return v___x_538_;
}
else
{
lean_object* v_head_539_; lean_object* v_tail_540_; lean_object* v_head_541_; lean_object* v_tail_542_; uint8_t v___x_543_; 
v_head_539_ = lean_ctor_get(v_x_534_, 0);
v_tail_540_ = lean_ctor_get(v_x_534_, 1);
v_head_541_ = lean_ctor_get(v_x_535_, 0);
v_tail_542_ = lean_ctor_get(v_x_535_, 1);
v___x_543_ = lean_name_eq(v_head_539_, v_head_541_);
if (v___x_543_ == 0)
{
return v___x_543_;
}
else
{
v_x_534_ = v_tail_540_;
v_x_535_ = v_tail_542_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
uint8_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_x_545_, v_x_546_);
lean_dec(v_x_546_);
lean_dec(v_x_545_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object* v_levelParams_552_, lean_object* v_type_553_, lean_object* v_value_554_, lean_object* v_kind_x3f_555_, uint8_t v_cache_556_, uint8_t v_inferRfl_557_, uint8_t v_forceExpose_558_, uint8_t v_defeq_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_env_567_; lean_object* v___x_568_; lean_object* v_asyncMode_569_; uint8_t v_isExporting_570_; lean_object* v___x_571_; lean_object* v___y_573_; uint8_t v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_616_; uint8_t v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; uint8_t v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; uint8_t v___y_667_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; uint8_t v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; uint8_t v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; uint8_t v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_778_; lean_object* v___y_779_; uint8_t v___y_780_; lean_object* v___x_794_; lean_object* v___y_796_; lean_object* v___y_797_; uint8_t v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; uint8_t v___y_839_; 
v___x_565_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_566_ = lean_st_ref_get(v_a_563_);
v_env_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc_ref_n(v_env_567_, 2);
lean_dec(v___x_566_);
v___x_568_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_569_ = lean_ctor_get(v___x_568_, 2);
v_isExporting_570_ = lean_ctor_get_uint8(v_env_567_, sizeof(void*)*8);
v___x_571_ = lean_box(0);
v___x_794_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_565_, v___x_568_, v_env_567_, v_asyncMode_569_, v___x_571_);
if (v_isExporting_570_ == 0)
{
uint8_t v___x_843_; 
v___x_843_ = 1;
v___y_839_ = v___x_843_;
goto v___jp_838_;
}
else
{
uint8_t v___x_844_; 
v___x_844_ = 0;
v___y_839_ = v___x_844_;
goto v___jp_838_;
}
v___jp_572_:
{
lean_object* v___x_578_; lean_object* v_env_579_; lean_object* v_nextMacroScope_580_; lean_object* v_ngen_581_; lean_object* v_auxDeclNGen_582_; lean_object* v_traceState_583_; lean_object* v_recordedDeps_584_; lean_object* v_messages_585_; lean_object* v_infoState_586_; lean_object* v_snapshotTasks_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_613_; 
v___x_578_ = lean_st_ref_take(v___y_577_);
v_env_579_ = lean_ctor_get(v___x_578_, 0);
v_nextMacroScope_580_ = lean_ctor_get(v___x_578_, 1);
v_ngen_581_ = lean_ctor_get(v___x_578_, 2);
v_auxDeclNGen_582_ = lean_ctor_get(v___x_578_, 3);
v_traceState_583_ = lean_ctor_get(v___x_578_, 4);
v_recordedDeps_584_ = lean_ctor_get(v___x_578_, 6);
v_messages_585_ = lean_ctor_get(v___x_578_, 7);
v_infoState_586_ = lean_ctor_get(v___x_578_, 8);
v_snapshotTasks_587_ = lean_ctor_get(v___x_578_, 9);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v___x_578_, 5);
lean_dec(v_unused_614_);
v___x_589_ = v___x_578_;
v_isShared_590_ = v_isSharedCheck_613_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_snapshotTasks_587_);
lean_inc(v_infoState_586_);
lean_inc(v_messages_585_);
lean_inc(v_recordedDeps_584_);
lean_inc(v_traceState_583_);
lean_inc(v_auxDeclNGen_582_);
lean_inc(v_ngen_581_);
lean_inc(v_nextMacroScope_580_);
lean_inc(v_env_579_);
lean_dec(v___x_578_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_613_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_591_ = l_Lean_EnvExtension_modifyState___redArg(v___x_568_, v_env_579_, v___y_575_, v_asyncMode_569_, v___x_571_, v___y_574_);
v___x_592_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 5, v___x_592_);
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_594_ = v___x_589_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_nextMacroScope_580_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_ngen_581_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_auxDeclNGen_582_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_traceState_583_);
lean_ctor_set(v_reuseFailAlloc_612_, 5, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_612_, 6, v_recordedDeps_584_);
lean_ctor_set(v_reuseFailAlloc_612_, 7, v_messages_585_);
lean_ctor_set(v_reuseFailAlloc_612_, 8, v_infoState_586_);
lean_ctor_set(v_reuseFailAlloc_612_, 9, v_snapshotTasks_587_);
v___x_594_ = v_reuseFailAlloc_612_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v_mctx_597_; lean_object* v_zetaDeltaFVarIds_598_; lean_object* v_postponed_599_; lean_object* v_diag_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_610_; 
v___x_595_ = lean_st_ref_put(v___y_577_, v___x_594_);
v___x_596_ = lean_st_ref_take(v___y_576_);
v_mctx_597_ = lean_ctor_get(v___x_596_, 0);
v_zetaDeltaFVarIds_598_ = lean_ctor_get(v___x_596_, 2);
v_postponed_599_ = lean_ctor_get(v___x_596_, 3);
v_diag_600_ = lean_ctor_get(v___x_596_, 4);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_596_, 1);
lean_dec(v_unused_611_);
v___x_602_ = v___x_596_;
v_isShared_603_ = v_isSharedCheck_610_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_diag_600_);
lean_inc(v_postponed_599_);
lean_inc(v_zetaDeltaFVarIds_598_);
lean_inc(v_mctx_597_);
lean_dec(v___x_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_610_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_mctx_597_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_zetaDeltaFVarIds_598_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_postponed_599_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_diag_600_);
v___x_606_ = v_reuseFailAlloc_609_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_st_ref_put(v___y_576_, v___x_606_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___y_573_);
return v___x_608_;
}
}
}
}
}
v___jp_615_:
{
if (v_inferRfl_557_ == 0)
{
v___y_573_ = v___y_616_;
v___y_574_ = v___y_617_;
v___y_575_ = v___y_618_;
v___y_576_ = v___y_620_;
v___y_577_ = v___y_622_;
goto v___jp_572_;
}
else
{
lean_object* v___x_623_; 
lean_inc(v___y_616_);
v___x_623_ = l_Lean_inferDefEqAttr(v___y_616_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_dec_ref_known(v___x_623_, 1);
v___y_573_ = v___y_616_;
v___y_574_ = v___y_617_;
v___y_575_ = v___y_618_;
v___y_576_ = v___y_620_;
v___y_577_ = v___y_622_;
goto v___jp_572_;
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v___y_618_);
lean_dec(v___y_616_);
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
v___jp_632_:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_addDecl(v___y_640_, v_forceExpose_558_, v___y_638_, v___y_633_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_dec_ref_known(v___x_641_, 1);
if (v_defeq_559_ == 0)
{
v___y_616_ = v___y_636_;
v___y_617_ = v___y_637_;
v___y_618_ = v___y_639_;
v___y_619_ = v___y_635_;
v___y_620_ = v___y_634_;
v___y_621_ = v___y_638_;
v___y_622_ = v___y_633_;
goto v___jp_615_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = l_Lean_defeqAttr;
lean_inc(v___y_636_);
v___x_643_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_642_, v___y_636_, v___y_635_, v___y_634_, v___y_638_, v___y_633_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_dec_ref_known(v___x_643_, 1);
v___y_616_ = v___y_636_;
v___y_617_ = v___y_637_;
v___y_618_ = v___y_639_;
v___y_619_ = v___y_635_;
v___y_620_ = v___y_634_;
v___y_621_ = v___y_638_;
v___y_622_ = v___y_633_;
goto v___jp_615_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref(v___y_639_);
lean_dec(v___y_636_);
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v___y_639_);
lean_dec(v___y_636_);
v_a_652_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_641_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_641_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
v___jp_660_:
{
uint8_t v___x_668_; 
v___x_668_ = 1;
if (v___y_667_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
lean_inc_n(v___y_664_, 2);
v___x_669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_669_, 0, v___y_664_);
lean_ctor_set(v___x_669_, 1, v_levelParams_552_);
lean_ctor_set(v___x_669_, 2, v_type_553_);
v___x_670_ = lean_box(0);
v___x_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_671_, 0, v___y_664_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_672_, 0, v___x_669_);
lean_ctor_set(v___x_672_, 1, v_value_554_);
lean_ctor_set(v___x_672_, 2, v___x_671_);
v___x_673_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
v___y_633_ = v___y_661_;
v___y_634_ = v___y_663_;
v___y_635_ = v___y_662_;
v___y_636_ = v___y_664_;
v___y_637_ = v___x_668_;
v___y_638_ = v___y_665_;
v___y_639_ = v___y_666_;
v___y_640_ = v___x_673_;
goto v___jp_632_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_inc_n(v___y_664_, 2);
v___x_674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_674_, 0, v___y_664_);
lean_ctor_set(v___x_674_, 1, v_levelParams_552_);
lean_ctor_set(v___x_674_, 2, v_type_553_);
v___x_675_ = lean_box(0);
v___x_676_ = 0;
v___x_677_ = lean_box(0);
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v___y_664_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_679_, 0, v___x_674_);
lean_ctor_set(v___x_679_, 1, v_value_554_);
lean_ctor_set(v___x_679_, 2, v___x_675_);
lean_ctor_set(v___x_679_, 3, v___x_678_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*4, v___x_676_);
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
v___y_633_ = v___y_661_;
v___y_634_ = v___y_663_;
v___y_635_ = v___y_662_;
v___y_636_ = v___y_664_;
v___y_637_ = v___x_668_;
v___y_638_ = v___y_665_;
v___y_639_ = v___y_666_;
v___y_640_ = v___x_680_;
goto v___jp_632_;
}
}
v___jp_681_:
{
lean_object* v___x_688_; lean_object* v_a_689_; lean_object* v___f_690_; uint8_t v___x_691_; 
v___x_688_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_683_, v___y_687_);
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_n(v_a_689_, 2);
lean_dec_ref(v___x_688_);
lean_inc(v_levelParams_552_);
v___f_690_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_690_, 0, v_a_689_);
lean_closure_set(v___f_690_, 1, v_levelParams_552_);
lean_closure_set(v___f_690_, 2, v___y_682_);
lean_inc_ref(v_env_567_);
v___x_691_ = l_Lean_Environment_hasUnsafe(v_env_567_, v_type_553_);
if (v___x_691_ == 0)
{
uint8_t v___x_692_; 
v___x_692_ = l_Lean_Environment_hasUnsafe(v_env_567_, v_value_554_);
v___y_661_ = v___y_687_;
v___y_662_ = v___y_684_;
v___y_663_ = v___y_685_;
v___y_664_ = v_a_689_;
v___y_665_ = v___y_686_;
v___y_666_ = v___f_690_;
v___y_667_ = v___x_692_;
goto v___jp_660_;
}
else
{
lean_dec_ref(v_env_567_);
v___y_661_ = v___y_687_;
v___y_662_ = v___y_684_;
v___y_663_ = v___y_685_;
v___y_664_ = v_a_689_;
v___y_665_ = v___y_686_;
v___y_666_ = v___f_690_;
v___y_667_ = v___x_691_;
goto v___jp_660_;
}
}
v___jp_693_:
{
lean_object* v___x_699_; lean_object* v_env_700_; lean_object* v_nextMacroScope_701_; lean_object* v_ngen_702_; lean_object* v_auxDeclNGen_703_; lean_object* v_traceState_704_; lean_object* v_recordedDeps_705_; lean_object* v_messages_706_; lean_object* v_infoState_707_; lean_object* v_snapshotTasks_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_734_; 
v___x_699_ = lean_st_ref_take(v___y_698_);
v_env_700_ = lean_ctor_get(v___x_699_, 0);
v_nextMacroScope_701_ = lean_ctor_get(v___x_699_, 1);
v_ngen_702_ = lean_ctor_get(v___x_699_, 2);
v_auxDeclNGen_703_ = lean_ctor_get(v___x_699_, 3);
v_traceState_704_ = lean_ctor_get(v___x_699_, 4);
v_recordedDeps_705_ = lean_ctor_get(v___x_699_, 6);
v_messages_706_ = lean_ctor_get(v___x_699_, 7);
v_infoState_707_ = lean_ctor_get(v___x_699_, 8);
v_snapshotTasks_708_ = lean_ctor_get(v___x_699_, 9);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___x_699_, 5);
lean_dec(v_unused_735_);
v___x_710_ = v___x_699_;
v_isShared_711_ = v_isSharedCheck_734_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_snapshotTasks_708_);
lean_inc(v_infoState_707_);
lean_inc(v_messages_706_);
lean_inc(v_recordedDeps_705_);
lean_inc(v_traceState_704_);
lean_inc(v_auxDeclNGen_703_);
lean_inc(v_ngen_702_);
lean_inc(v_nextMacroScope_701_);
lean_inc(v_env_700_);
lean_dec(v___x_699_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_734_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_712_ = l_Lean_EnvExtension_modifyState___redArg(v___x_568_, v_env_700_, v___y_696_, v_asyncMode_569_, v___x_571_, v___y_694_);
v___x_713_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 5, v___x_713_);
lean_ctor_set(v___x_710_, 0, v___x_712_);
v___x_715_ = v___x_710_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_nextMacroScope_701_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_ngen_702_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_auxDeclNGen_703_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_traceState_704_);
lean_ctor_set(v_reuseFailAlloc_733_, 5, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_733_, 6, v_recordedDeps_705_);
lean_ctor_set(v_reuseFailAlloc_733_, 7, v_messages_706_);
lean_ctor_set(v_reuseFailAlloc_733_, 8, v_infoState_707_);
lean_ctor_set(v_reuseFailAlloc_733_, 9, v_snapshotTasks_708_);
v___x_715_ = v_reuseFailAlloc_733_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_mctx_718_; lean_object* v_zetaDeltaFVarIds_719_; lean_object* v_postponed_720_; lean_object* v_diag_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_731_; 
v___x_716_ = lean_st_ref_put(v___y_698_, v___x_715_);
v___x_717_ = lean_st_ref_take(v___y_697_);
v_mctx_718_ = lean_ctor_get(v___x_717_, 0);
v_zetaDeltaFVarIds_719_ = lean_ctor_get(v___x_717_, 2);
v_postponed_720_ = lean_ctor_get(v___x_717_, 3);
v_diag_721_ = lean_ctor_get(v___x_717_, 4);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v___x_717_, 1);
lean_dec(v_unused_732_);
v___x_723_ = v___x_717_;
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_diag_721_);
lean_inc(v_postponed_720_);
lean_inc(v_zetaDeltaFVarIds_719_);
lean_inc(v_mctx_718_);
lean_dec(v___x_717_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_mctx_718_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_zetaDeltaFVarIds_719_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_postponed_720_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_diag_721_);
v___x_727_ = v_reuseFailAlloc_730_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_st_ref_put(v___y_697_, v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___y_695_);
return v___x_729_;
}
}
}
}
}
v___jp_736_:
{
if (v_inferRfl_557_ == 0)
{
v___y_694_ = v___y_737_;
v___y_695_ = v___y_738_;
v___y_696_ = v___y_739_;
v___y_697_ = v___y_741_;
v___y_698_ = v___y_743_;
goto v___jp_693_;
}
else
{
lean_object* v___x_744_; 
lean_inc(v___y_738_);
v___x_744_ = l_Lean_inferDefEqAttr(v___y_738_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_dec_ref_known(v___x_744_, 1);
v___y_694_ = v___y_737_;
v___y_695_ = v___y_738_;
v___y_696_ = v___y_739_;
v___y_697_ = v___y_741_;
v___y_698_ = v___y_743_;
goto v___jp_693_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
v___jp_753_:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_addDecl(v___y_757_, v_forceExpose_558_, v_a_562_, v_a_563_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_dec_ref_known(v___x_758_, 1);
if (v_defeq_559_ == 0)
{
v___y_737_ = v___y_754_;
v___y_738_ = v___y_755_;
v___y_739_ = v___y_756_;
v___y_740_ = v_a_560_;
v___y_741_ = v_a_561_;
v___y_742_ = v_a_562_;
v___y_743_ = v_a_563_;
goto v___jp_736_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = l_Lean_defeqAttr;
lean_inc(v___y_755_);
v___x_760_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_759_, v___y_755_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_dec_ref_known(v___x_760_, 1);
v___y_737_ = v___y_754_;
v___y_738_ = v___y_755_;
v___y_739_ = v___y_756_;
v___y_740_ = v_a_560_;
v___y_741_ = v_a_561_;
v___y_742_ = v_a_562_;
v___y_743_ = v_a_563_;
goto v___jp_736_;
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
v_a_769_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_758_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_758_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
v___jp_777_:
{
uint8_t v___x_781_; 
v___x_781_ = 1;
if (v___y_780_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_inc_n(v___y_778_, 2);
v___x_782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_782_, 0, v___y_778_);
lean_ctor_set(v___x_782_, 1, v_levelParams_552_);
lean_ctor_set(v___x_782_, 2, v_type_553_);
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_784_, 0, v___y_778_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v_value_554_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
v___x_786_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
v___y_754_ = v___x_781_;
v___y_755_ = v___y_778_;
v___y_756_ = v___y_779_;
v___y_757_ = v___x_786_;
goto v___jp_753_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_inc_n(v___y_778_, 2);
v___x_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_787_, 0, v___y_778_);
lean_ctor_set(v___x_787_, 1, v_levelParams_552_);
lean_ctor_set(v___x_787_, 2, v_type_553_);
v___x_788_ = lean_box(0);
v___x_789_ = 0;
v___x_790_ = lean_box(0);
v___x_791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_791_, 0, v___y_778_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_792_, 0, v___x_787_);
lean_ctor_set(v___x_792_, 1, v_value_554_);
lean_ctor_set(v___x_792_, 2, v___x_788_);
lean_ctor_set(v___x_792_, 3, v___x_791_);
lean_ctor_set_uint8(v___x_792_, sizeof(void*)*4, v___x_789_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
v___y_754_ = v___x_781_;
v___y_755_ = v___y_778_;
v___y_756_ = v___y_779_;
v___y_757_ = v___x_793_;
goto v___jp_753_;
}
}
v___jp_795_:
{
if (v___y_798_ == 0)
{
lean_dec(v___x_794_);
v___y_682_ = v___y_796_;
v___y_683_ = v___y_797_;
v___y_684_ = v___y_799_;
v___y_685_ = v___y_800_;
v___y_686_ = v___y_801_;
v___y_687_ = v___y_802_;
goto v___jp_681_;
}
else
{
uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = 0;
lean_inc_ref(v_type_553_);
v___x_804_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_804_, 0, v_type_553_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*1, v___x_803_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*1 + 1, v_defeq_559_);
v___x_805_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_794_, v___x_804_);
lean_dec_ref_known(v___x_804_, 1);
lean_dec(v___x_794_);
if (lean_obj_tag(v___x_805_) == 1)
{
lean_object* v_val_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_816_; 
v_val_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_816_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_val_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_fst_810_; lean_object* v_snd_811_; uint8_t v___x_812_; 
v_fst_810_ = lean_ctor_get(v_val_806_, 0);
lean_inc(v_fst_810_);
v_snd_811_ = lean_ctor_get(v_val_806_, 1);
lean_inc(v_snd_811_);
lean_dec(v_val_806_);
v___x_812_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_552_, v_snd_811_);
lean_dec(v_snd_811_);
if (v___x_812_ == 0)
{
lean_dec(v_fst_810_);
lean_del_object(v___x_808_);
v___y_682_ = v___y_796_;
v___y_683_ = v___y_797_;
v___y_684_ = v___y_799_;
v___y_685_ = v___y_800_;
v___y_686_ = v___y_801_;
v___y_687_ = v___y_802_;
goto v___jp_681_;
}
else
{
lean_object* v___x_814_; 
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec_ref(v_env_567_);
lean_dec_ref(v_value_554_);
lean_dec_ref(v_type_553_);
lean_dec(v_levelParams_552_);
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 0);
lean_ctor_set(v___x_808_, 0, v_fst_810_);
v___x_814_ = v___x_808_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_fst_810_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_dec(v___x_805_);
v___y_682_ = v___y_796_;
v___y_683_ = v___y_797_;
v___y_684_ = v___y_799_;
v___y_685_ = v___y_800_;
v___y_686_ = v___y_801_;
v___y_687_ = v___y_802_;
goto v___jp_681_;
}
}
}
v___jp_817_:
{
if (v_cache_556_ == 0)
{
lean_object* v___x_821_; lean_object* v_a_822_; lean_object* v___f_823_; uint8_t v___x_824_; 
lean_dec(v___x_794_);
v___x_821_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_820_, v_a_563_);
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc_n(v_a_822_, 2);
lean_dec_ref(v___x_821_);
lean_inc(v_levelParams_552_);
v___f_823_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_823_, 0, v_a_822_);
lean_closure_set(v___f_823_, 1, v_levelParams_552_);
lean_closure_set(v___f_823_, 2, v___y_819_);
lean_inc_ref(v_env_567_);
v___x_824_ = l_Lean_Environment_hasUnsafe(v_env_567_, v_type_553_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; 
v___x_825_ = l_Lean_Environment_hasUnsafe(v_env_567_, v_value_554_);
v___y_778_ = v_a_822_;
v___y_779_ = v___f_823_;
v___y_780_ = v___x_825_;
goto v___jp_777_;
}
else
{
lean_dec_ref(v_env_567_);
v___y_778_ = v_a_822_;
v___y_779_ = v___f_823_;
v___y_780_ = v___x_824_;
goto v___jp_777_;
}
}
else
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_794_, v___y_819_);
if (lean_obj_tag(v___x_826_) == 1)
{
lean_object* v_val_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_837_; 
v_val_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_837_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_val_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_fst_831_; lean_object* v_snd_832_; uint8_t v___x_833_; 
v_fst_831_ = lean_ctor_get(v_val_827_, 0);
lean_inc(v_fst_831_);
v_snd_832_ = lean_ctor_get(v_val_827_, 1);
lean_inc(v_snd_832_);
lean_dec(v_val_827_);
v___x_833_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_552_, v_snd_832_);
lean_dec(v_snd_832_);
if (v___x_833_ == 0)
{
lean_dec(v_fst_831_);
lean_del_object(v___x_829_);
v___y_796_ = v___y_819_;
v___y_797_ = v___y_820_;
v___y_798_ = v___y_818_;
v___y_799_ = v_a_560_;
v___y_800_ = v_a_561_;
v___y_801_ = v_a_562_;
v___y_802_ = v_a_563_;
goto v___jp_795_;
}
else
{
lean_object* v___x_835_; 
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___x_794_);
lean_dec_ref(v_env_567_);
lean_dec_ref(v_value_554_);
lean_dec_ref(v_type_553_);
lean_dec(v_levelParams_552_);
if (v_isShared_830_ == 0)
{
lean_ctor_set_tag(v___x_829_, 0);
lean_ctor_set(v___x_829_, 0, v_fst_831_);
v___x_835_ = v___x_829_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_fst_831_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_dec(v___x_826_);
v___y_796_ = v___y_819_;
v___y_797_ = v___y_820_;
v___y_798_ = v___y_818_;
v___y_799_ = v_a_560_;
v___y_800_ = v_a_561_;
v___y_801_ = v_a_562_;
v___y_802_ = v_a_563_;
goto v___jp_795_;
}
}
}
v___jp_838_:
{
lean_object* v___x_840_; 
lean_inc_ref(v_type_553_);
v___x_840_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_840_, 0, v_type_553_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*1, v___y_839_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*1 + 1, v_defeq_559_);
if (lean_obj_tag(v_kind_x3f_555_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__1));
v___y_818_ = v___y_839_;
v___y_819_ = v___x_840_;
v___y_820_ = v___x_841_;
goto v___jp_817_;
}
else
{
lean_object* v_val_842_; 
v_val_842_ = lean_ctor_get(v_kind_x3f_555_, 0);
lean_inc(v_val_842_);
lean_dec_ref_known(v_kind_x3f_555_, 1);
v___y_818_ = v___y_839_;
v___y_819_ = v___x_840_;
v___y_820_ = v_val_842_;
goto v___jp_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_845_, lean_object* v_type_846_, lean_object* v_value_847_, lean_object* v_kind_x3f_848_, lean_object* v_cache_849_, lean_object* v_inferRfl_850_, lean_object* v_forceExpose_851_, lean_object* v_defeq_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
uint8_t v_cache_boxed_858_; uint8_t v_inferRfl_boxed_859_; uint8_t v_forceExpose_boxed_860_; uint8_t v_defeq_boxed_861_; lean_object* v_res_862_; 
v_cache_boxed_858_ = lean_unbox(v_cache_849_);
v_inferRfl_boxed_859_ = lean_unbox(v_inferRfl_850_);
v_forceExpose_boxed_860_ = lean_unbox(v_forceExpose_851_);
v_defeq_boxed_861_ = lean_unbox(v_defeq_852_);
v_res_862_ = l_Lean_Meta_mkAuxLemma(v_levelParams_845_, v_type_846_, v_value_847_, v_kind_x3f_848_, v_cache_boxed_858_, v_inferRfl_boxed_859_, v_forceExpose_boxed_860_, v_defeq_boxed_861_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_864_, v_x_865_, v_x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(v_00_u03b2_872_, v_x_873_, v_x_874_);
lean_dec_ref(v_x_874_);
lean_dec_ref(v_x_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, size_t v_x_878_, size_t v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_877_, v_x_878_, v_x_879_, v_x_880_, v_x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
size_t v_x_6565__boxed_889_; size_t v_x_6566__boxed_890_; lean_object* v_res_891_; 
v_x_6565__boxed_889_ = lean_unbox_usize(v_x_885_);
lean_dec(v_x_885_);
v_x_6566__boxed_890_ = lean_unbox_usize(v_x_886_);
lean_dec(v_x_886_);
v_res_891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_883_, v_x_884_, v_x_6565__boxed_889_, v_x_6566__boxed_890_, v_x_887_, v_x_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b1_892_, lean_object* v_attrName_893_, lean_object* v_declName_894_, lean_object* v_asyncPrefix_x3f_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_893_, v_declName_894_, v_asyncPrefix_x3f_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_902_, lean_object* v_attrName_903_, lean_object* v_declName_904_, lean_object* v_asyncPrefix_x3f_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b1_902_, v_attrName_903_, v_declName_904_, v_asyncPrefix_x3f_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(lean_object* v_00_u03b1_912_, lean_object* v_attrName_913_, lean_object* v_declName_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_913_, v_declName_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___boxed(lean_object* v_00_u03b1_921_, lean_object* v_attrName_922_, lean_object* v_declName_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(v_00_u03b1_921_, v_attrName_922_, v_declName_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, size_t v_x_932_, lean_object* v_x_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_931_, v_x_932_, v_x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object* v_00_u03b2_935_, lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
size_t v_x_6616__boxed_939_; lean_object* v_res_940_; 
v_x_6616__boxed_939_ = lean_unbox_usize(v_x_937_);
lean_dec(v_x_937_);
v_res_940_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(v_00_u03b2_935_, v_x_936_, v_x_6616__boxed_939_, v_x_938_);
lean_dec_ref(v_x_938_);
lean_dec_ref(v_x_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_941_, lean_object* v_n_942_, lean_object* v_k_943_, lean_object* v_v_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_942_, v_k_943_, v_v_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_946_, size_t v_depth_947_, lean_object* v_keys_948_, lean_object* v_vals_949_, lean_object* v_heq_950_, lean_object* v_i_951_, lean_object* v_entries_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_947_, v_keys_948_, v_vals_949_, v_i_951_, v_entries_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_954_, lean_object* v_depth_955_, lean_object* v_keys_956_, lean_object* v_vals_957_, lean_object* v_heq_958_, lean_object* v_i_959_, lean_object* v_entries_960_){
_start:
{
size_t v_depth_boxed_961_; lean_object* v_res_962_; 
v_depth_boxed_961_ = lean_unbox_usize(v_depth_955_);
lean_dec(v_depth_955_);
v_res_962_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_954_, v_depth_boxed_961_, v_keys_956_, v_vals_957_, v_heq_958_, v_i_959_, v_entries_960_);
lean_dec_ref(v_vals_957_);
lean_dec_ref(v_keys_956_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_963_, lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_971_, lean_object* v_msg_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b1_971_, v_msg_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_979_, lean_object* v_keys_980_, lean_object* v_vals_981_, lean_object* v_heq_982_, lean_object* v_i_983_, lean_object* v_k_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_980_, v_vals_981_, v_i_983_, v_k_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_986_, lean_object* v_keys_987_, lean_object* v_vals_988_, lean_object* v_heq_989_, lean_object* v_i_990_, lean_object* v_k_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(v_00_u03b2_986_, v_keys_987_, v_vals_988_, v_heq_989_, v_i_990_, v_k_991_);
lean_dec_ref(v_k_991_);
lean_dec_ref(v_vals_988_);
lean_dec_ref(v_keys_987_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_x_994_, v_x_995_, v_x_996_, v_x_997_);
return v___x_998_;
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
