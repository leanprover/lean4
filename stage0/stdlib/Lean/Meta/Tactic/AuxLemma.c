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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2;
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; 
v___x_141_ = ((size_t)5ULL);
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_shift_left(v___x_142_, v___x_141_);
return v___x_143_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; 
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0);
v___x_146_ = lean_usize_sub(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object* v_x_148_, size_t v_x_149_, size_t v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v_es_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; lean_object* v_j_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_es_153_ = lean_ctor_get(v_x_148_, 0);
v___x_154_ = ((size_t)5ULL);
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1);
v___x_157_ = lean_usize_land(v_x_149_, v___x_156_);
v_j_158_ = lean_usize_to_nat(v___x_157_);
v___x_159_ = lean_array_get_size(v_es_153_);
v___x_160_ = lean_nat_dec_lt(v_j_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec(v_j_158_);
lean_dec(v_x_152_);
lean_dec_ref(v_x_151_);
return v_x_148_;
}
else
{
lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_197_; 
lean_inc_ref(v_es_153_);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; 
v_unused_198_ = lean_ctor_get(v_x_148_, 0);
lean_dec(v_unused_198_);
v___x_162_ = v_x_148_;
v_isShared_163_ = v_isSharedCheck_197_;
goto v_resetjp_161_;
}
else
{
lean_dec(v_x_148_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_197_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v_v_164_; lean_object* v___x_165_; lean_object* v_xs_x27_166_; lean_object* v___y_168_; 
v_v_164_ = lean_array_fget(v_es_153_, v_j_158_);
v___x_165_ = lean_box(0);
v_xs_x27_166_ = lean_array_fset(v_es_153_, v_j_158_, v___x_165_);
switch(lean_obj_tag(v_v_164_))
{
case 0:
{
lean_object* v_key_173_; lean_object* v_val_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_184_; 
v_key_173_ = lean_ctor_get(v_v_164_, 0);
v_val_174_ = lean_ctor_get(v_v_164_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_v_164_);
if (v_isSharedCheck_184_ == 0)
{
v___x_176_ = v_v_164_;
v_isShared_177_ = v_isSharedCheck_184_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_val_174_);
lean_inc(v_key_173_);
lean_dec(v_v_164_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_184_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
uint8_t v___x_178_; 
v___x_178_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_151_, v_key_173_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_del_object(v___x_176_);
v___x_179_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_173_, v_val_174_, v_x_151_, v_x_152_);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
v___y_168_ = v___x_180_;
goto v___jp_167_;
}
else
{
lean_object* v___x_182_; 
lean_dec(v_val_174_);
lean_dec(v_key_173_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v_x_152_);
lean_ctor_set(v___x_176_, 0, v_x_151_);
v___x_182_ = v___x_176_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_x_151_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_x_152_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
v___y_168_ = v___x_182_;
goto v___jp_167_;
}
}
}
}
case 1:
{
lean_object* v_node_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_195_; 
v_node_185_ = lean_ctor_get(v_v_164_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v_v_164_);
if (v_isSharedCheck_195_ == 0)
{
v___x_187_ = v_v_164_;
v_isShared_188_ = v_isSharedCheck_195_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_node_185_);
lean_dec(v_v_164_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_195_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
size_t v___x_189_; size_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_189_ = lean_usize_shift_right(v_x_149_, v___x_154_);
v___x_190_ = lean_usize_add(v_x_150_, v___x_155_);
v___x_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_node_185_, v___x_189_, v___x_190_, v_x_151_, v_x_152_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_191_);
v___x_193_ = v___x_187_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
v___y_168_ = v___x_193_;
goto v___jp_167_;
}
}
}
default: 
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v_x_151_);
lean_ctor_set(v___x_196_, 1, v_x_152_);
v___y_168_ = v___x_196_;
goto v___jp_167_;
}
}
v___jp_167_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_array_fset(v_xs_x27_166_, v_j_158_, v___y_168_);
lean_dec(v_j_158_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_169_);
v___x_171_ = v___x_162_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
else
{
lean_object* v_ks_199_; lean_object* v_vs_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_220_; 
v_ks_199_ = lean_ctor_get(v_x_148_, 0);
v_vs_200_ = lean_ctor_get(v_x_148_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_220_ == 0)
{
v___x_202_ = v_x_148_;
v_isShared_203_ = v_isSharedCheck_220_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_vs_200_);
lean_inc(v_ks_199_);
lean_dec(v_x_148_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_220_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_ks_199_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_vs_200_);
v___x_205_ = v_reuseFailAlloc_219_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v_newNode_206_; uint8_t v___y_208_; size_t v___x_214_; uint8_t v___x_215_; 
v_newNode_206_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v___x_205_, v_x_151_, v_x_152_);
v___x_214_ = ((size_t)7ULL);
v___x_215_ = lean_usize_dec_le(v___x_214_, v_x_150_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_216_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_206_);
v___x_217_ = lean_unsigned_to_nat(4u);
v___x_218_ = lean_nat_dec_lt(v___x_216_, v___x_217_);
lean_dec(v___x_216_);
v___y_208_ = v___x_218_;
goto v___jp_207_;
}
else
{
v___y_208_ = v___x_215_;
goto v___jp_207_;
}
v___jp_207_:
{
if (v___y_208_ == 0)
{
lean_object* v_ks_209_; lean_object* v_vs_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_ks_209_ = lean_ctor_get(v_newNode_206_, 0);
lean_inc_ref(v_ks_209_);
v_vs_210_ = lean_ctor_get(v_newNode_206_, 1);
lean_inc_ref(v_vs_210_);
lean_dec_ref(v_newNode_206_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2);
v___x_213_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_x_150_, v_ks_209_, v_vs_210_, v___x_211_, v___x_212_);
lean_dec_ref(v_vs_210_);
lean_dec_ref(v_ks_209_);
return v___x_213_;
}
else
{
return v_newNode_206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t v_depth_221_, lean_object* v_keys_222_, lean_object* v_vals_223_, lean_object* v_i_224_, lean_object* v_entries_225_){
_start:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_array_get_size(v_keys_222_);
v___x_227_ = lean_nat_dec_lt(v_i_224_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec(v_i_224_);
return v_entries_225_;
}
else
{
lean_object* v_k_228_; lean_object* v_v_229_; uint64_t v___x_230_; size_t v_h_231_; size_t v___x_232_; lean_object* v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v_h_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_k_228_ = lean_array_fget_borrowed(v_keys_222_, v_i_224_);
v_v_229_ = lean_array_fget_borrowed(v_vals_223_, v_i_224_);
v___x_230_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_k_228_);
v_h_231_ = lean_uint64_to_usize(v___x_230_);
v___x_232_ = ((size_t)5ULL);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_sub(v_depth_221_, v___x_234_);
v___x_236_ = lean_usize_mul(v___x_232_, v___x_235_);
v_h_237_ = lean_usize_shift_right(v_h_231_, v___x_236_);
v___x_238_ = lean_nat_add(v_i_224_, v___x_233_);
lean_dec(v_i_224_);
lean_inc(v_v_229_);
lean_inc(v_k_228_);
v___x_239_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_entries_225_, v_h_237_, v_depth_221_, v_k_228_, v_v_229_);
v_i_224_ = v___x_238_;
v_entries_225_ = v___x_239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_241_, lean_object* v_keys_242_, lean_object* v_vals_243_, lean_object* v_i_244_, lean_object* v_entries_245_){
_start:
{
size_t v_depth_boxed_246_; lean_object* v_res_247_; 
v_depth_boxed_246_ = lean_unbox_usize(v_depth_241_);
lean_dec(v_depth_241_);
v_res_247_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_boxed_246_, v_keys_242_, v_vals_243_, v_i_244_, v_entries_245_);
lean_dec_ref(v_vals_243_);
lean_dec_ref(v_keys_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
size_t v_x_6178__boxed_253_; size_t v_x_6179__boxed_254_; lean_object* v_res_255_; 
v_x_6178__boxed_253_ = lean_unbox_usize(v_x_249_);
lean_dec(v_x_249_);
v_x_6179__boxed_254_ = lean_unbox_usize(v_x_250_);
lean_dec(v_x_250_);
v_res_255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_248_, v_x_6178__boxed_253_, v_x_6179__boxed_254_, v_x_251_, v_x_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint64_t v___x_259_; size_t v___x_260_; size_t v___x_261_; lean_object* v___x_262_; 
v___x_259_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_257_);
v___x_260_ = lean_uint64_to_usize(v___x_259_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_256_, v___x_260_, v___x_261_, v_x_257_, v_x_258_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object* v_a_263_, lean_object* v_levelParams_264_, lean_object* v___x_265_, lean_object* v_x_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v_a_263_);
lean_ctor_set(v___x_267_, 1, v_levelParams_264_);
v___x_268_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_266_, v___x_265_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(lean_object* v_msgData_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; lean_object* v_env_276_; lean_object* v___x_277_; lean_object* v_mctx_278_; lean_object* v_lctx_279_; lean_object* v_options_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_275_ = lean_st_ref_get(v___y_273_);
v_env_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc_ref(v_env_276_);
lean_dec(v___x_275_);
v___x_277_ = lean_st_ref_get(v___y_271_);
v_mctx_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc_ref(v_mctx_278_);
lean_dec(v___x_277_);
v_lctx_279_ = lean_ctor_get(v___y_270_, 2);
v_options_280_ = lean_ctor_get(v___y_272_, 2);
lean_inc_ref(v_options_280_);
lean_inc_ref(v_lctx_279_);
v___x_281_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_281_, 0, v_env_276_);
lean_ctor_set(v___x_281_, 1, v_mctx_278_);
lean_ctor_set(v___x_281_, 2, v_lctx_279_);
lean_ctor_set(v___x_281_, 3, v_options_280_);
v___x_282_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v_msgData_269_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_msgData_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msgData_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(lean_object* v_msg_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_ref_297_; lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_307_; 
v_ref_297_ = lean_ctor_get(v___y_294_, 5);
v___x_298_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msg_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_307_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_307_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_307_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
lean_inc(v_ref_297_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_ref_297_);
lean_ctor_set(v___x_303_, 1, v_a_299_);
if (v_isShared_302_ == 0)
{
lean_ctor_set_tag(v___x_301_, 1);
lean_ctor_set(v___x_301_, 0, v___x_303_);
v___x_305_ = v___x_301_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_314_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0));
v___x_317_ = l_Lean_stringToMessageData(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2));
v___x_320_ = l_Lean_stringToMessageData(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4));
v___x_323_ = l_Lean_stringToMessageData(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6));
v___x_326_ = l_Lean_stringToMessageData(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8));
v___x_329_ = l_Lean_stringToMessageData(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(lean_object* v_attrName_330_, lean_object* v_declName_331_, lean_object* v_asyncPrefix_x3f_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___y_339_; 
if (lean_obj_tag(v_asyncPrefix_x3f_332_) == 0)
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_MessageData_nil;
v___y_339_ = v___x_352_;
goto v___jp_338_;
}
else
{
lean_object* v_val_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_val_353_ = lean_ctor_get(v_asyncPrefix_x3f_332_, 0);
lean_inc(v_val_353_);
lean_dec_ref(v_asyncPrefix_x3f_332_);
v___x_354_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7);
v___x_355_ = l_Lean_MessageData_ofName(v_val_353_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___y_339_ = v___x_358_;
goto v___jp_338_;
}
v___jp_338_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_340_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_341_ = l_Lean_MessageData_ofName(v_attrName_330_);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = 0;
v___x_346_ = l_Lean_MessageData_ofConstName(v_declName_331_, v___x_345_);
v___x_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_344_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5);
v___x_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___y_339_);
v___x_351_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_350_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object* v_attrName_359_, lean_object* v_declName_360_, lean_object* v_asyncPrefix_x3f_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_359_, v_declName_360_, v_asyncPrefix_x3f_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_367_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(lean_object* v_attrName_371_, lean_object* v_declName_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_378_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_379_ = l_Lean_MessageData_ofName(v_attrName_371_);
v___x_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = 0;
v___x_384_ = l_Lean_MessageData_ofConstName(v_declName_372_, v___x_383_);
v___x_385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_382_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1);
v___x_387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_387_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___boxed(lean_object* v_attrName_389_, lean_object* v_declName_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_389_, v_declName_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_396_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_397_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_403_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
lean_ctor_set(v___x_403_, 2, v___x_402_);
lean_ctor_set(v___x_403_, 3, v___x_402_);
lean_ctor_set(v___x_403_, 4, v___x_402_);
lean_ctor_set(v___x_403_, 5, v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object* v_attr_404_, lean_object* v_decl_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___x_454_; lean_object* v_env_455_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___x_470_; 
v___x_454_ = lean_st_ref_get(v___y_409_);
v_env_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc_ref(v_env_455_);
lean_dec(v___x_454_);
v___x_470_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_455_, v_decl_405_);
if (lean_obj_tag(v___x_470_) == 0)
{
v___y_457_ = v___y_406_;
v___y_458_ = v___y_407_;
v___y_459_ = v___y_408_;
v___y_460_ = v___y_409_;
goto v___jp_456_;
}
else
{
lean_object* v_attr_471_; lean_object* v_toAttributeImplCore_472_; lean_object* v_name_473_; lean_object* v___x_474_; 
lean_dec_ref(v___x_470_);
lean_dec_ref(v_env_455_);
v_attr_471_ = lean_ctor_get(v_attr_404_, 0);
lean_inc_ref(v_attr_471_);
lean_dec_ref(v_attr_404_);
v_toAttributeImplCore_472_ = lean_ctor_get(v_attr_471_, 0);
lean_inc_ref(v_toAttributeImplCore_472_);
lean_dec_ref(v_attr_471_);
v_name_473_ = lean_ctor_get(v_toAttributeImplCore_472_, 1);
lean_inc(v_name_473_);
lean_dec_ref(v_toAttributeImplCore_472_);
v___x_474_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_name_473_, v_decl_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v___x_474_;
}
v___jp_411_:
{
lean_object* v___x_414_; lean_object* v_ext_415_; lean_object* v_toEnvExtension_416_; lean_object* v_env_417_; lean_object* v_nextMacroScope_418_; lean_object* v_ngen_419_; lean_object* v_auxDeclNGen_420_; lean_object* v_traceState_421_; lean_object* v_messages_422_; lean_object* v_infoState_423_; lean_object* v_snapshotTasks_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_452_; 
v___x_414_ = lean_st_ref_take(v___y_413_);
v_ext_415_ = lean_ctor_get(v_attr_404_, 1);
lean_inc_ref(v_ext_415_);
lean_dec_ref(v_attr_404_);
v_toEnvExtension_416_ = lean_ctor_get(v_ext_415_, 0);
v_env_417_ = lean_ctor_get(v___x_414_, 0);
v_nextMacroScope_418_ = lean_ctor_get(v___x_414_, 1);
v_ngen_419_ = lean_ctor_get(v___x_414_, 2);
v_auxDeclNGen_420_ = lean_ctor_get(v___x_414_, 3);
v_traceState_421_ = lean_ctor_get(v___x_414_, 4);
v_messages_422_ = lean_ctor_get(v___x_414_, 6);
v_infoState_423_ = lean_ctor_get(v___x_414_, 7);
v_snapshotTasks_424_ = lean_ctor_get(v___x_414_, 8);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; 
v_unused_453_ = lean_ctor_get(v___x_414_, 5);
lean_dec(v_unused_453_);
v___x_426_ = v___x_414_;
v_isShared_427_ = v_isSharedCheck_452_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snapshotTasks_424_);
lean_inc(v_infoState_423_);
lean_inc(v_messages_422_);
lean_inc(v_traceState_421_);
lean_inc(v_auxDeclNGen_420_);
lean_inc(v_ngen_419_);
lean_inc(v_nextMacroScope_418_);
lean_inc(v_env_417_);
lean_dec(v___x_414_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_452_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_asyncMode_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v_asyncMode_428_ = lean_ctor_get(v_toEnvExtension_416_, 2);
lean_inc(v_asyncMode_428_);
lean_inc(v_decl_405_);
v___x_429_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_415_, v_env_417_, v_decl_405_, v_asyncMode_428_, v_decl_405_);
lean_dec(v_asyncMode_428_);
v___x_430_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 5, v___x_430_);
lean_ctor_set(v___x_426_, 0, v___x_429_);
v___x_432_ = v___x_426_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_nextMacroScope_418_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_ngen_419_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_auxDeclNGen_420_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_traceState_421_);
lean_ctor_set(v_reuseFailAlloc_451_, 5, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_451_, 6, v_messages_422_);
lean_ctor_set(v_reuseFailAlloc_451_, 7, v_infoState_423_);
lean_ctor_set(v_reuseFailAlloc_451_, 8, v_snapshotTasks_424_);
v___x_432_ = v_reuseFailAlloc_451_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_mctx_435_; lean_object* v_zetaDeltaFVarIds_436_; lean_object* v_postponed_437_; lean_object* v_diag_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_449_; 
v___x_433_ = lean_st_ref_set(v___y_413_, v___x_432_);
v___x_434_ = lean_st_ref_take(v___y_412_);
v_mctx_435_ = lean_ctor_get(v___x_434_, 0);
v_zetaDeltaFVarIds_436_ = lean_ctor_get(v___x_434_, 2);
v_postponed_437_ = lean_ctor_get(v___x_434_, 3);
v_diag_438_ = lean_ctor_get(v___x_434_, 4);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_434_, 1);
lean_dec(v_unused_450_);
v___x_440_ = v___x_434_;
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_diag_438_);
lean_inc(v_postponed_437_);
lean_inc(v_zetaDeltaFVarIds_436_);
lean_inc(v_mctx_435_);
lean_dec(v___x_434_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_mctx_435_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_zetaDeltaFVarIds_436_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_postponed_437_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v_diag_438_);
v___x_444_ = v_reuseFailAlloc_448_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_st_ref_set(v___y_412_, v___x_444_);
v___x_446_ = lean_box(0);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
}
}
}
v___jp_456_:
{
lean_object* v_ext_461_; lean_object* v_toEnvExtension_462_; lean_object* v_attr_463_; lean_object* v_asyncMode_464_; uint8_t v___x_465_; 
v_ext_461_ = lean_ctor_get(v_attr_404_, 1);
v_toEnvExtension_462_ = lean_ctor_get(v_ext_461_, 0);
v_attr_463_ = lean_ctor_get(v_attr_404_, 0);
v_asyncMode_464_ = lean_ctor_get(v_toEnvExtension_462_, 2);
lean_inc(v_decl_405_);
lean_inc_ref(v_env_455_);
v___x_465_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_455_, v_decl_405_, v_asyncMode_464_);
if (v___x_465_ == 0)
{
lean_object* v_toAttributeImplCore_466_; lean_object* v_name_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_inc_ref(v_attr_463_);
lean_dec_ref(v_attr_404_);
v_toAttributeImplCore_466_ = lean_ctor_get(v_attr_463_, 0);
lean_inc_ref(v_toAttributeImplCore_466_);
lean_dec_ref(v_attr_463_);
v_name_467_ = lean_ctor_get(v_toAttributeImplCore_466_, 1);
lean_inc(v_name_467_);
lean_dec_ref(v_toAttributeImplCore_466_);
v___x_468_ = l_Lean_Environment_asyncPrefix_x3f(v_env_455_);
v___x_469_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_name_467_, v_decl_405_, v___x_468_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
return v___x_469_;
}
else
{
lean_dec_ref(v_env_455_);
v___y_412_ = v___y_458_;
v___y_413_ = v___y_460_;
goto v___jp_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object* v_attr_475_, lean_object* v_decl_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v_attr_475_, v_decl_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(lean_object* v_keys_483_, lean_object* v_vals_484_, lean_object* v_i_485_, lean_object* v_k_486_){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_array_get_size(v_keys_483_);
v___x_488_ = lean_nat_dec_lt(v_i_485_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v_i_485_);
v___x_489_ = lean_box(0);
return v___x_489_;
}
else
{
lean_object* v_k_x27_490_; uint8_t v___x_491_; 
v_k_x27_490_ = lean_array_fget_borrowed(v_keys_483_, v_i_485_);
v___x_491_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_k_486_, v_k_x27_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_nat_add(v_i_485_, v___x_492_);
lean_dec(v_i_485_);
v_i_485_ = v___x_493_;
goto _start;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_array_fget_borrowed(v_vals_484_, v_i_485_);
lean_dec(v_i_485_);
lean_inc(v___x_495_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_keys_497_, lean_object* v_vals_498_, lean_object* v_i_499_, lean_object* v_k_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_497_, v_vals_498_, v_i_499_, v_k_500_);
lean_dec_ref(v_k_500_);
lean_dec_ref(v_vals_498_);
lean_dec_ref(v_keys_497_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(lean_object* v_x_502_, size_t v_x_503_, lean_object* v_x_504_){
_start:
{
if (lean_obj_tag(v_x_502_) == 0)
{
lean_object* v_es_505_; lean_object* v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; lean_object* v_j_510_; lean_object* v___x_511_; 
v_es_505_ = lean_ctor_get(v_x_502_, 0);
v___x_506_ = lean_box(2);
v___x_507_ = ((size_t)5ULL);
v___x_508_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1);
v___x_509_ = lean_usize_land(v_x_503_, v___x_508_);
v_j_510_ = lean_usize_to_nat(v___x_509_);
v___x_511_ = lean_array_get_borrowed(v___x_506_, v_es_505_, v_j_510_);
lean_dec(v_j_510_);
switch(lean_obj_tag(v___x_511_))
{
case 0:
{
lean_object* v_key_512_; lean_object* v_val_513_; uint8_t v___x_514_; 
v_key_512_ = lean_ctor_get(v___x_511_, 0);
v_val_513_ = lean_ctor_get(v___x_511_, 1);
v___x_514_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_504_, v_key_512_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
v___x_515_ = lean_box(0);
return v___x_515_;
}
else
{
lean_object* v___x_516_; 
lean_inc(v_val_513_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v_val_513_);
return v___x_516_;
}
}
case 1:
{
lean_object* v_node_517_; size_t v___x_518_; 
v_node_517_ = lean_ctor_get(v___x_511_, 0);
v___x_518_ = lean_usize_shift_right(v_x_503_, v___x_507_);
v_x_502_ = v_node_517_;
v_x_503_ = v___x_518_;
goto _start;
}
default: 
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
}
}
else
{
lean_object* v_ks_521_; lean_object* v_vs_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_ks_521_ = lean_ctor_get(v_x_502_, 0);
v_vs_522_ = lean_ctor_get(v_x_502_, 1);
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_ks_521_, v_vs_522_, v___x_523_, v_x_504_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(lean_object* v_x_525_, lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
size_t v_x_6733__boxed_528_; lean_object* v_res_529_; 
v_x_6733__boxed_528_ = lean_unbox_usize(v_x_526_);
lean_dec(v_x_526_);
v_res_529_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_525_, v_x_6733__boxed_528_, v_x_527_);
lean_dec_ref(v_x_527_);
lean_dec_ref(v_x_525_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
uint64_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; 
v___x_532_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_531_);
v___x_533_ = lean_uint64_to_usize(v___x_532_);
v___x_534_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_530_, v___x_533_, v_x_531_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg___boxed(lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_535_, v_x_536_);
lean_dec_ref(v_x_536_);
lean_dec_ref(v_x_535_);
return v_res_537_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
if (lean_obj_tag(v_x_539_) == 0)
{
uint8_t v___x_540_; 
v___x_540_ = 1;
return v___x_540_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = 0;
return v___x_541_;
}
}
else
{
if (lean_obj_tag(v_x_539_) == 0)
{
uint8_t v___x_542_; 
v___x_542_ = 0;
return v___x_542_;
}
else
{
lean_object* v_head_543_; lean_object* v_tail_544_; lean_object* v_head_545_; lean_object* v_tail_546_; uint8_t v___x_547_; 
v_head_543_ = lean_ctor_get(v_x_538_, 0);
v_tail_544_ = lean_ctor_get(v_x_538_, 1);
v_head_545_ = lean_ctor_get(v_x_539_, 0);
v_tail_546_ = lean_ctor_get(v_x_539_, 1);
v___x_547_ = lean_name_eq(v_head_543_, v_head_545_);
if (v___x_547_ == 0)
{
return v___x_547_;
}
else
{
v_x_538_ = v_tail_544_;
v_x_539_ = v_tail_546_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
uint8_t v_res_551_; lean_object* v_r_552_; 
v_res_551_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_x_549_, v_x_550_);
lean_dec(v_x_550_);
lean_dec(v_x_549_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object* v_levelParams_556_, lean_object* v_type_557_, lean_object* v_value_558_, lean_object* v_kind_x3f_559_, uint8_t v_cache_560_, uint8_t v_inferRfl_561_, uint8_t v_forceExpose_562_, uint8_t v_defeq_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_569_; lean_object* v_env_570_; lean_object* v___x_571_; lean_object* v_asyncMode_572_; uint8_t v_isExporting_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; uint8_t v___y_667_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_773_; lean_object* v___y_774_; uint8_t v___y_775_; lean_object* v___x_788_; lean_object* v___y_790_; lean_object* v___y_791_; uint8_t v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_812_; uint8_t v___y_813_; lean_object* v___y_814_; uint8_t v___y_833_; 
v___x_569_ = lean_st_ref_get(v_a_567_);
v_env_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref_n(v_env_570_, 2);
lean_dec(v___x_569_);
v___x_571_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_572_ = lean_ctor_get(v___x_571_, 2);
v_isExporting_573_ = lean_ctor_get_uint8(v_env_570_, sizeof(void*)*8);
v___x_574_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_575_ = lean_box(0);
v___x_788_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_574_, v___x_571_, v_env_570_, v_asyncMode_572_, v___x_575_);
if (v_isExporting_573_ == 0)
{
uint8_t v___x_837_; 
v___x_837_ = 1;
v___y_833_ = v___x_837_;
goto v___jp_832_;
}
else
{
uint8_t v___x_838_; 
v___x_838_ = 0;
v___y_833_ = v___x_838_;
goto v___jp_832_;
}
v___jp_576_:
{
lean_object* v___x_581_; lean_object* v_env_582_; lean_object* v_nextMacroScope_583_; lean_object* v_ngen_584_; lean_object* v_auxDeclNGen_585_; lean_object* v_traceState_586_; lean_object* v_messages_587_; lean_object* v_infoState_588_; lean_object* v_snapshotTasks_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_615_; 
v___x_581_ = lean_st_ref_take(v___y_580_);
v_env_582_ = lean_ctor_get(v___x_581_, 0);
v_nextMacroScope_583_ = lean_ctor_get(v___x_581_, 1);
v_ngen_584_ = lean_ctor_get(v___x_581_, 2);
v_auxDeclNGen_585_ = lean_ctor_get(v___x_581_, 3);
v_traceState_586_ = lean_ctor_get(v___x_581_, 4);
v_messages_587_ = lean_ctor_get(v___x_581_, 6);
v_infoState_588_ = lean_ctor_get(v___x_581_, 7);
v_snapshotTasks_589_ = lean_ctor_get(v___x_581_, 8);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_581_, 5);
lean_dec(v_unused_616_);
v___x_591_ = v___x_581_;
v_isShared_592_ = v_isSharedCheck_615_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_snapshotTasks_589_);
lean_inc(v_infoState_588_);
lean_inc(v_messages_587_);
lean_inc(v_traceState_586_);
lean_inc(v_auxDeclNGen_585_);
lean_inc(v_ngen_584_);
lean_inc(v_nextMacroScope_583_);
lean_inc(v_env_582_);
lean_dec(v___x_581_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_615_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_593_ = l_Lean_EnvExtension_modifyState___redArg(v___x_571_, v_env_582_, v___y_577_, v_asyncMode_572_, v___x_575_);
v___x_594_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 5, v___x_594_);
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_596_ = v___x_591_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_nextMacroScope_583_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_ngen_584_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_auxDeclNGen_585_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_traceState_586_);
lean_ctor_set(v_reuseFailAlloc_614_, 5, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_614_, 6, v_messages_587_);
lean_ctor_set(v_reuseFailAlloc_614_, 7, v_infoState_588_);
lean_ctor_set(v_reuseFailAlloc_614_, 8, v_snapshotTasks_589_);
v___x_596_ = v_reuseFailAlloc_614_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_mctx_599_; lean_object* v_zetaDeltaFVarIds_600_; lean_object* v_postponed_601_; lean_object* v_diag_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_612_; 
v___x_597_ = lean_st_ref_set(v___y_580_, v___x_596_);
v___x_598_ = lean_st_ref_take(v___y_579_);
v_mctx_599_ = lean_ctor_get(v___x_598_, 0);
v_zetaDeltaFVarIds_600_ = lean_ctor_get(v___x_598_, 2);
v_postponed_601_ = lean_ctor_get(v___x_598_, 3);
v_diag_602_ = lean_ctor_get(v___x_598_, 4);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_598_, 1);
lean_dec(v_unused_613_);
v___x_604_ = v___x_598_;
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_diag_602_);
lean_inc(v_postponed_601_);
lean_inc(v_zetaDeltaFVarIds_600_);
lean_inc(v_mctx_599_);
lean_dec(v___x_598_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_mctx_599_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_zetaDeltaFVarIds_600_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_postponed_601_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_diag_602_);
v___x_608_ = v_reuseFailAlloc_611_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_st_ref_set(v___y_579_, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___y_578_);
return v___x_610_;
}
}
}
}
}
v___jp_617_:
{
if (v_inferRfl_561_ == 0)
{
v___y_577_ = v___y_618_;
v___y_578_ = v___y_619_;
v___y_579_ = v___y_621_;
v___y_580_ = v___y_623_;
goto v___jp_576_;
}
else
{
lean_object* v___x_624_; 
lean_inc(v___y_619_);
v___x_624_ = l_Lean_inferDefEqAttr(v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_dec_ref(v___x_624_);
v___y_577_ = v___y_618_;
v___y_578_ = v___y_619_;
v___y_579_ = v___y_621_;
v___y_580_ = v___y_623_;
goto v___jp_576_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
v___jp_633_:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_addDecl(v___y_640_, v_forceExpose_562_, v___y_636_, v___y_638_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_dec_ref(v___x_641_);
if (v_defeq_563_ == 0)
{
v___y_618_ = v___y_637_;
v___y_619_ = v___y_639_;
v___y_620_ = v___y_635_;
v___y_621_ = v___y_634_;
v___y_622_ = v___y_636_;
v___y_623_ = v___y_638_;
goto v___jp_617_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = l_Lean_defeqAttr;
lean_inc(v___y_639_);
v___x_643_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_642_, v___y_639_, v___y_635_, v___y_634_, v___y_636_, v___y_638_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_dec_ref(v___x_643_);
v___y_618_ = v___y_637_;
v___y_619_ = v___y_639_;
v___y_620_ = v___y_635_;
v___y_621_ = v___y_634_;
v___y_622_ = v___y_636_;
v___y_623_ = v___y_638_;
goto v___jp_617_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v___y_639_);
lean_dec_ref(v___y_637_);
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
lean_dec(v___y_639_);
lean_dec_ref(v___y_637_);
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
if (v___y_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_inc_n(v___y_666_, 2);
v___x_668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_668_, 0, v___y_666_);
lean_ctor_set(v___x_668_, 1, v_levelParams_556_);
lean_ctor_set(v___x_668_, 2, v_type_557_);
v___x_669_ = lean_box(0);
v___x_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_670_, 0, v___y_666_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_671_, 0, v___x_668_);
lean_ctor_set(v___x_671_, 1, v_value_558_);
lean_ctor_set(v___x_671_, 2, v___x_670_);
v___x_672_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
v___y_634_ = v___y_662_;
v___y_635_ = v___y_661_;
v___y_636_ = v___y_663_;
v___y_637_ = v___y_665_;
v___y_638_ = v___y_664_;
v___y_639_ = v___y_666_;
v___y_640_ = v___x_672_;
goto v___jp_633_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_inc_n(v___y_666_, 2);
v___x_673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_673_, 0, v___y_666_);
lean_ctor_set(v___x_673_, 1, v_levelParams_556_);
lean_ctor_set(v___x_673_, 2, v_type_557_);
v___x_674_ = lean_box(0);
v___x_675_ = 0;
v___x_676_ = lean_box(0);
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v___y_666_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_678_, 0, v___x_673_);
lean_ctor_set(v___x_678_, 1, v_value_558_);
lean_ctor_set(v___x_678_, 2, v___x_674_);
lean_ctor_set(v___x_678_, 3, v___x_677_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*4, v___x_675_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
v___y_634_ = v___y_662_;
v___y_635_ = v___y_661_;
v___y_636_ = v___y_663_;
v___y_637_ = v___y_665_;
v___y_638_ = v___y_664_;
v___y_639_ = v___y_666_;
v___y_640_ = v___x_679_;
goto v___jp_633_;
}
}
v___jp_680_:
{
lean_object* v___x_687_; lean_object* v_a_688_; lean_object* v___f_689_; uint8_t v___x_690_; 
v___x_687_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_682_, v___y_686_);
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc_n(v_a_688_, 2);
lean_dec_ref(v___x_687_);
lean_inc(v_levelParams_556_);
v___f_689_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_689_, 0, v_a_688_);
lean_closure_set(v___f_689_, 1, v_levelParams_556_);
lean_closure_set(v___f_689_, 2, v___y_681_);
lean_inc_ref(v_env_570_);
v___x_690_ = l_Lean_Environment_hasUnsafe(v_env_570_, v_type_557_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; 
v___x_691_ = l_Lean_Environment_hasUnsafe(v_env_570_, v_value_558_);
v___y_661_ = v___y_683_;
v___y_662_ = v___y_684_;
v___y_663_ = v___y_685_;
v___y_664_ = v___y_686_;
v___y_665_ = v___f_689_;
v___y_666_ = v_a_688_;
v___y_667_ = v___x_691_;
goto v___jp_660_;
}
else
{
lean_dec_ref(v_env_570_);
v___y_661_ = v___y_683_;
v___y_662_ = v___y_684_;
v___y_663_ = v___y_685_;
v___y_664_ = v___y_686_;
v___y_665_ = v___f_689_;
v___y_666_ = v_a_688_;
v___y_667_ = v___x_690_;
goto v___jp_660_;
}
}
v___jp_692_:
{
lean_object* v___x_697_; lean_object* v_env_698_; lean_object* v_nextMacroScope_699_; lean_object* v_ngen_700_; lean_object* v_auxDeclNGen_701_; lean_object* v_traceState_702_; lean_object* v_messages_703_; lean_object* v_infoState_704_; lean_object* v_snapshotTasks_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_731_; 
v___x_697_ = lean_st_ref_take(v___y_696_);
v_env_698_ = lean_ctor_get(v___x_697_, 0);
v_nextMacroScope_699_ = lean_ctor_get(v___x_697_, 1);
v_ngen_700_ = lean_ctor_get(v___x_697_, 2);
v_auxDeclNGen_701_ = lean_ctor_get(v___x_697_, 3);
v_traceState_702_ = lean_ctor_get(v___x_697_, 4);
v_messages_703_ = lean_ctor_get(v___x_697_, 6);
v_infoState_704_ = lean_ctor_get(v___x_697_, 7);
v_snapshotTasks_705_ = lean_ctor_get(v___x_697_, 8);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v___x_697_, 5);
lean_dec(v_unused_732_);
v___x_707_ = v___x_697_;
v_isShared_708_ = v_isSharedCheck_731_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_snapshotTasks_705_);
lean_inc(v_infoState_704_);
lean_inc(v_messages_703_);
lean_inc(v_traceState_702_);
lean_inc(v_auxDeclNGen_701_);
lean_inc(v_ngen_700_);
lean_inc(v_nextMacroScope_699_);
lean_inc(v_env_698_);
lean_dec(v___x_697_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_731_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_709_ = l_Lean_EnvExtension_modifyState___redArg(v___x_571_, v_env_698_, v___y_694_, v_asyncMode_572_, v___x_575_);
v___x_710_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 5, v___x_710_);
lean_ctor_set(v___x_707_, 0, v___x_709_);
v___x_712_ = v___x_707_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_nextMacroScope_699_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_ngen_700_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_auxDeclNGen_701_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_traceState_702_);
lean_ctor_set(v_reuseFailAlloc_730_, 5, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_730_, 6, v_messages_703_);
lean_ctor_set(v_reuseFailAlloc_730_, 7, v_infoState_704_);
lean_ctor_set(v_reuseFailAlloc_730_, 8, v_snapshotTasks_705_);
v___x_712_ = v_reuseFailAlloc_730_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_mctx_715_; lean_object* v_zetaDeltaFVarIds_716_; lean_object* v_postponed_717_; lean_object* v_diag_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_728_; 
v___x_713_ = lean_st_ref_set(v___y_696_, v___x_712_);
v___x_714_ = lean_st_ref_take(v___y_695_);
v_mctx_715_ = lean_ctor_get(v___x_714_, 0);
v_zetaDeltaFVarIds_716_ = lean_ctor_get(v___x_714_, 2);
v_postponed_717_ = lean_ctor_get(v___x_714_, 3);
v_diag_718_ = lean_ctor_get(v___x_714_, 4);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v___x_714_, 1);
lean_dec(v_unused_729_);
v___x_720_ = v___x_714_;
v_isShared_721_ = v_isSharedCheck_728_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_diag_718_);
lean_inc(v_postponed_717_);
lean_inc(v_zetaDeltaFVarIds_716_);
lean_inc(v_mctx_715_);
lean_dec(v___x_714_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_728_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_mctx_715_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_zetaDeltaFVarIds_716_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_postponed_717_);
lean_ctor_set(v_reuseFailAlloc_727_, 4, v_diag_718_);
v___x_724_ = v_reuseFailAlloc_727_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_st_ref_set(v___y_695_, v___x_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___y_693_);
return v___x_726_;
}
}
}
}
}
v___jp_733_:
{
if (v_inferRfl_561_ == 0)
{
v___y_693_ = v___y_734_;
v___y_694_ = v___y_735_;
v___y_695_ = v___y_737_;
v___y_696_ = v___y_739_;
goto v___jp_692_;
}
else
{
lean_object* v___x_740_; 
lean_inc(v___y_734_);
v___x_740_ = l_Lean_inferDefEqAttr(v___y_734_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_dec_ref(v___x_740_);
v___y_693_ = v___y_734_;
v___y_694_ = v___y_735_;
v___y_695_ = v___y_737_;
v___y_696_ = v___y_739_;
goto v___jp_692_;
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
v___jp_749_:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_addDecl(v___y_752_, v_forceExpose_562_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_dec_ref(v___x_753_);
if (v_defeq_563_ == 0)
{
v___y_734_ = v___y_750_;
v___y_735_ = v___y_751_;
v___y_736_ = v_a_564_;
v___y_737_ = v_a_565_;
v___y_738_ = v_a_566_;
v___y_739_ = v_a_567_;
goto v___jp_733_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = l_Lean_defeqAttr;
lean_inc(v___y_750_);
v___x_755_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_754_, v___y_750_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_dec_ref(v___x_755_);
v___y_734_ = v___y_750_;
v___y_735_ = v___y_751_;
v___y_736_ = v_a_564_;
v___y_737_ = v_a_565_;
v___y_738_ = v_a_566_;
v___y_739_ = v_a_567_;
goto v___jp_733_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
v_a_764_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_753_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_753_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
v___jp_772_:
{
if (v___y_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_inc_n(v___y_773_, 2);
v___x_776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_776_, 0, v___y_773_);
lean_ctor_set(v___x_776_, 1, v_levelParams_556_);
lean_ctor_set(v___x_776_, 2, v_type_557_);
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v___y_773_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_779_, 0, v___x_776_);
lean_ctor_set(v___x_779_, 1, v_value_558_);
lean_ctor_set(v___x_779_, 2, v___x_778_);
v___x_780_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
v___y_750_ = v___y_773_;
v___y_751_ = v___y_774_;
v___y_752_ = v___x_780_;
goto v___jp_749_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
lean_inc_n(v___y_773_, 2);
v___x_781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_781_, 0, v___y_773_);
lean_ctor_set(v___x_781_, 1, v_levelParams_556_);
lean_ctor_set(v___x_781_, 2, v_type_557_);
v___x_782_ = lean_box(0);
v___x_783_ = 0;
v___x_784_ = lean_box(0);
v___x_785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_785_, 0, v___y_773_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_786_, 0, v___x_781_);
lean_ctor_set(v___x_786_, 1, v_value_558_);
lean_ctor_set(v___x_786_, 2, v___x_782_);
lean_ctor_set(v___x_786_, 3, v___x_785_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*4, v___x_783_);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
v___y_750_ = v___y_773_;
v___y_751_ = v___y_774_;
v___y_752_ = v___x_787_;
goto v___jp_749_;
}
}
v___jp_789_:
{
if (v___y_792_ == 0)
{
lean_dec(v___x_788_);
v___y_681_ = v___y_790_;
v___y_682_ = v___y_791_;
v___y_683_ = v___y_793_;
v___y_684_ = v___y_794_;
v___y_685_ = v___y_795_;
v___y_686_ = v___y_796_;
goto v___jp_680_;
}
else
{
uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = 0;
lean_inc_ref(v_type_557_);
v___x_798_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_798_, 0, v_type_557_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*1, v___x_797_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*1 + 1, v_defeq_563_);
v___x_799_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_788_, v___x_798_);
lean_dec_ref(v___x_798_);
lean_dec(v___x_788_);
if (lean_obj_tag(v___x_799_) == 1)
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_810_; 
v_val_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_810_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_fst_804_; lean_object* v_snd_805_; uint8_t v___x_806_; 
v_fst_804_ = lean_ctor_get(v_val_800_, 0);
lean_inc(v_fst_804_);
v_snd_805_ = lean_ctor_get(v_val_800_, 1);
lean_inc(v_snd_805_);
lean_dec(v_val_800_);
v___x_806_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_556_, v_snd_805_);
lean_dec(v_snd_805_);
if (v___x_806_ == 0)
{
lean_dec(v_fst_804_);
lean_del_object(v___x_802_);
v___y_681_ = v___y_790_;
v___y_682_ = v___y_791_;
v___y_683_ = v___y_793_;
v___y_684_ = v___y_794_;
v___y_685_ = v___y_795_;
v___y_686_ = v___y_796_;
goto v___jp_680_;
}
else
{
lean_object* v___x_808_; 
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec_ref(v_env_570_);
lean_dec_ref(v_value_558_);
lean_dec_ref(v_type_557_);
lean_dec(v_levelParams_556_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 0);
lean_ctor_set(v___x_802_, 0, v_fst_804_);
v___x_808_ = v___x_802_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_fst_804_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_dec(v___x_799_);
v___y_681_ = v___y_790_;
v___y_682_ = v___y_791_;
v___y_683_ = v___y_793_;
v___y_684_ = v___y_794_;
v___y_685_ = v___y_795_;
v___y_686_ = v___y_796_;
goto v___jp_680_;
}
}
}
v___jp_811_:
{
if (v_cache_560_ == 0)
{
lean_object* v___x_815_; lean_object* v_a_816_; lean_object* v___f_817_; uint8_t v___x_818_; 
lean_dec(v___x_788_);
v___x_815_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_814_, v_a_567_);
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc_n(v_a_816_, 2);
lean_dec_ref(v___x_815_);
lean_inc(v_levelParams_556_);
v___f_817_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_817_, 0, v_a_816_);
lean_closure_set(v___f_817_, 1, v_levelParams_556_);
lean_closure_set(v___f_817_, 2, v___y_812_);
lean_inc_ref(v_env_570_);
v___x_818_ = l_Lean_Environment_hasUnsafe(v_env_570_, v_type_557_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_Environment_hasUnsafe(v_env_570_, v_value_558_);
v___y_773_ = v_a_816_;
v___y_774_ = v___f_817_;
v___y_775_ = v___x_819_;
goto v___jp_772_;
}
else
{
lean_dec_ref(v_env_570_);
v___y_773_ = v_a_816_;
v___y_774_ = v___f_817_;
v___y_775_ = v___x_818_;
goto v___jp_772_;
}
}
else
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_788_, v___y_812_);
if (lean_obj_tag(v___x_820_) == 1)
{
lean_object* v_val_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_831_; 
v_val_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_831_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_val_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_fst_825_; lean_object* v_snd_826_; uint8_t v___x_827_; 
v_fst_825_ = lean_ctor_get(v_val_821_, 0);
lean_inc(v_fst_825_);
v_snd_826_ = lean_ctor_get(v_val_821_, 1);
lean_inc(v_snd_826_);
lean_dec(v_val_821_);
v___x_827_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_556_, v_snd_826_);
lean_dec(v_snd_826_);
if (v___x_827_ == 0)
{
lean_dec(v_fst_825_);
lean_del_object(v___x_823_);
v___y_790_ = v___y_812_;
v___y_791_ = v___y_814_;
v___y_792_ = v___y_813_;
v___y_793_ = v_a_564_;
v___y_794_ = v_a_565_;
v___y_795_ = v_a_566_;
v___y_796_ = v_a_567_;
goto v___jp_789_;
}
else
{
lean_object* v___x_829_; 
lean_dec(v___y_814_);
lean_dec_ref(v___y_812_);
lean_dec(v___x_788_);
lean_dec_ref(v_env_570_);
lean_dec_ref(v_value_558_);
lean_dec_ref(v_type_557_);
lean_dec(v_levelParams_556_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
lean_ctor_set(v___x_823_, 0, v_fst_825_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_fst_825_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_dec(v___x_820_);
v___y_790_ = v___y_812_;
v___y_791_ = v___y_814_;
v___y_792_ = v___y_813_;
v___y_793_ = v_a_564_;
v___y_794_ = v_a_565_;
v___y_795_ = v_a_566_;
v___y_796_ = v_a_567_;
goto v___jp_789_;
}
}
}
v___jp_832_:
{
lean_object* v___x_834_; 
lean_inc_ref(v_type_557_);
v___x_834_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_834_, 0, v_type_557_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*1, v___y_833_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*1 + 1, v_defeq_563_);
if (lean_obj_tag(v_kind_x3f_559_) == 0)
{
lean_object* v___x_835_; 
v___x_835_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__1));
v___y_812_ = v___x_834_;
v___y_813_ = v___y_833_;
v___y_814_ = v___x_835_;
goto v___jp_811_;
}
else
{
lean_object* v_val_836_; 
v_val_836_ = lean_ctor_get(v_kind_x3f_559_, 0);
lean_inc(v_val_836_);
lean_dec_ref(v_kind_x3f_559_);
v___y_812_ = v___x_834_;
v___y_813_ = v___y_833_;
v___y_814_ = v_val_836_;
goto v___jp_811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_839_, lean_object* v_type_840_, lean_object* v_value_841_, lean_object* v_kind_x3f_842_, lean_object* v_cache_843_, lean_object* v_inferRfl_844_, lean_object* v_forceExpose_845_, lean_object* v_defeq_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
uint8_t v_cache_boxed_852_; uint8_t v_inferRfl_boxed_853_; uint8_t v_forceExpose_boxed_854_; uint8_t v_defeq_boxed_855_; lean_object* v_res_856_; 
v_cache_boxed_852_ = lean_unbox(v_cache_843_);
v_inferRfl_boxed_853_ = lean_unbox(v_inferRfl_844_);
v_forceExpose_boxed_854_ = lean_unbox(v_forceExpose_845_);
v_defeq_boxed_855_ = lean_unbox(v_defeq_846_);
v_res_856_ = l_Lean_Meta_mkAuxLemma(v_levelParams_839_, v_type_840_, v_value_841_, v_kind_x3f_842_, v_cache_boxed_852_, v_inferRfl_boxed_853_, v_forceExpose_boxed_854_, v_defeq_boxed_855_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_858_, v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(v_00_u03b2_866_, v_x_867_, v_x_868_);
lean_dec_ref(v_x_868_);
lean_dec_ref(v_x_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, size_t v_x_872_, size_t v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_871_, v_x_872_, v_x_873_, v_x_874_, v_x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_877_, lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
size_t v_x_7370__boxed_883_; size_t v_x_7371__boxed_884_; lean_object* v_res_885_; 
v_x_7370__boxed_883_ = lean_unbox_usize(v_x_879_);
lean_dec(v_x_879_);
v_x_7371__boxed_884_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_res_885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_877_, v_x_878_, v_x_7370__boxed_883_, v_x_7371__boxed_884_, v_x_881_, v_x_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b1_886_, lean_object* v_attrName_887_, lean_object* v_declName_888_, lean_object* v_asyncPrefix_x3f_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_887_, v_declName_888_, v_asyncPrefix_x3f_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_896_, lean_object* v_attrName_897_, lean_object* v_declName_898_, lean_object* v_asyncPrefix_x3f_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b1_896_, v_attrName_897_, v_declName_898_, v_asyncPrefix_x3f_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(lean_object* v_00_u03b1_906_, lean_object* v_attrName_907_, lean_object* v_declName_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_907_, v_declName_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___boxed(lean_object* v_00_u03b1_915_, lean_object* v_attrName_916_, lean_object* v_declName_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(v_00_u03b1_915_, v_attrName_916_, v_declName_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object* v_00_u03b2_924_, lean_object* v_x_925_, size_t v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_925_, v_x_926_, v_x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object* v_00_u03b2_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
size_t v_x_7421__boxed_933_; lean_object* v_res_934_; 
v_x_7421__boxed_933_ = lean_unbox_usize(v_x_931_);
lean_dec(v_x_931_);
v_res_934_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(v_00_u03b2_929_, v_x_930_, v_x_7421__boxed_933_, v_x_932_);
lean_dec_ref(v_x_932_);
lean_dec_ref(v_x_930_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_935_, lean_object* v_n_936_, lean_object* v_k_937_, lean_object* v_v_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_936_, v_k_937_, v_v_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_940_, size_t v_depth_941_, lean_object* v_keys_942_, lean_object* v_vals_943_, lean_object* v_heq_944_, lean_object* v_i_945_, lean_object* v_entries_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_941_, v_keys_942_, v_vals_943_, v_i_945_, v_entries_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_948_, lean_object* v_depth_949_, lean_object* v_keys_950_, lean_object* v_vals_951_, lean_object* v_heq_952_, lean_object* v_i_953_, lean_object* v_entries_954_){
_start:
{
size_t v_depth_boxed_955_; lean_object* v_res_956_; 
v_depth_boxed_955_ = lean_unbox_usize(v_depth_949_);
lean_dec(v_depth_949_);
v_res_956_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_948_, v_depth_boxed_955_, v_keys_950_, v_vals_951_, v_heq_952_, v_i_953_, v_entries_954_);
lean_dec_ref(v_vals_951_);
lean_dec_ref(v_keys_950_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_957_, lean_object* v_msg_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_965_, lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b1_965_, v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_973_, lean_object* v_keys_974_, lean_object* v_vals_975_, lean_object* v_heq_976_, lean_object* v_i_977_, lean_object* v_k_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_974_, v_vals_975_, v_i_977_, v_k_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_980_, lean_object* v_keys_981_, lean_object* v_vals_982_, lean_object* v_heq_983_, lean_object* v_i_984_, lean_object* v_k_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(v_00_u03b2_980_, v_keys_981_, v_vals_982_, v_heq_983_, v_i_984_, v_k_985_);
lean_dec_ref(v_k_985_);
lean_dec_ref(v_vals_982_);
lean_dec_ref(v_keys_981_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_987_, lean_object* v_x_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_x_988_, v_x_989_, v_x_990_, v_x_991_);
return v___x_992_;
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
