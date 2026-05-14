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
lean_object* v___x_62_; lean_object* v_auxDeclNGen_63_; lean_object* v___x_64_; lean_object* v_env_65_; lean_object* v___x_66_; lean_object* v_fst_67_; lean_object* v_snd_68_; lean_object* v___x_69_; lean_object* v_env_70_; lean_object* v_nextMacroScope_71_; lean_object* v_ngen_72_; lean_object* v_traceState_73_; lean_object* v_cache_74_; lean_object* v_messages_75_; lean_object* v_infoState_76_; lean_object* v_snapshotTasks_77_; lean_object* v_newDecls_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_87_; 
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
v_newDecls_78_ = lean_ctor_get(v___x_69_, 9);
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
lean_inc(v_newDecls_78_);
lean_inc(v_snapshotTasks_77_);
lean_inc(v_infoState_76_);
lean_inc(v_messages_75_);
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
lean_ctor_set(v_reuseFailAlloc_86_, 6, v_messages_75_);
lean_ctor_set(v_reuseFailAlloc_86_, 7, v_infoState_76_);
lean_ctor_set(v_reuseFailAlloc_86_, 8, v_snapshotTasks_77_);
lean_ctor_set(v_reuseFailAlloc_86_, 9, v_newDecls_78_);
v___x_83_ = v_reuseFailAlloc_86_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_st_ref_set(v___y_60_, v___x_83_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; 
v___x_142_ = ((size_t)5ULL);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_shift_left(v___x_143_, v___x_142_);
return v___x_144_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; 
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0);
v___x_147_ = lean_usize_sub(v___x_146_, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object* v_x_149_, size_t v_x_150_, size_t v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v_es_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; size_t v___x_158_; lean_object* v_j_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_es_154_ = lean_ctor_get(v_x_149_, 0);
v___x_155_ = ((size_t)5ULL);
v___x_156_ = ((size_t)1ULL);
v___x_157_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1);
v___x_158_ = lean_usize_land(v_x_150_, v___x_157_);
v_j_159_ = lean_usize_to_nat(v___x_158_);
v___x_160_ = lean_array_get_size(v_es_154_);
v___x_161_ = lean_nat_dec_lt(v_j_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_dec(v_j_159_);
lean_dec(v_x_153_);
lean_dec_ref(v_x_152_);
return v_x_149_;
}
else
{
lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_198_; 
lean_inc_ref(v_es_154_);
v_isSharedCheck_198_ = !lean_is_exclusive(v_x_149_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v_x_149_, 0);
lean_dec(v_unused_199_);
v___x_163_ = v_x_149_;
v_isShared_164_ = v_isSharedCheck_198_;
goto v_resetjp_162_;
}
else
{
lean_dec(v_x_149_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_198_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_v_165_; lean_object* v___x_166_; lean_object* v_xs_x27_167_; lean_object* v___y_169_; 
v_v_165_ = lean_array_fget(v_es_154_, v_j_159_);
v___x_166_ = lean_box(0);
v_xs_x27_167_ = lean_array_fset(v_es_154_, v_j_159_, v___x_166_);
switch(lean_obj_tag(v_v_165_))
{
case 0:
{
lean_object* v_key_174_; lean_object* v_val_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_185_; 
v_key_174_ = lean_ctor_get(v_v_165_, 0);
v_val_175_ = lean_ctor_get(v_v_165_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_v_165_);
if (v_isSharedCheck_185_ == 0)
{
v___x_177_ = v_v_165_;
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_val_175_);
lean_inc(v_key_174_);
lean_dec(v_v_165_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
uint8_t v___x_179_; 
v___x_179_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_152_, v_key_174_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_del_object(v___x_177_);
v___x_180_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_174_, v_val_175_, v_x_152_, v_x_153_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
v___y_169_ = v___x_181_;
goto v___jp_168_;
}
else
{
lean_object* v___x_183_; 
lean_dec(v_val_175_);
lean_dec(v_key_174_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v_x_153_);
lean_ctor_set(v___x_177_, 0, v_x_152_);
v___x_183_ = v___x_177_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_x_152_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_x_153_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
v___y_169_ = v___x_183_;
goto v___jp_168_;
}
}
}
}
case 1:
{
lean_object* v_node_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_196_; 
v_node_186_ = lean_ctor_get(v_v_165_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v_v_165_);
if (v_isSharedCheck_196_ == 0)
{
v___x_188_ = v_v_165_;
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_node_186_);
lean_dec(v_v_165_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_190_ = lean_usize_shift_right(v_x_150_, v___x_155_);
v___x_191_ = lean_usize_add(v_x_151_, v___x_156_);
v___x_192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_node_186_, v___x_190_, v___x_191_, v_x_152_, v_x_153_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_192_);
v___x_194_ = v___x_188_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
v___y_169_ = v___x_194_;
goto v___jp_168_;
}
}
}
default: 
{
lean_object* v___x_197_; 
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v_x_152_);
lean_ctor_set(v___x_197_, 1, v_x_153_);
v___y_169_ = v___x_197_;
goto v___jp_168_;
}
}
v___jp_168_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_array_fset(v_xs_x27_167_, v_j_159_, v___y_169_);
lean_dec(v_j_159_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_170_);
v___x_172_ = v___x_163_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
else
{
lean_object* v_ks_200_; lean_object* v_vs_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_221_; 
v_ks_200_ = lean_ctor_get(v_x_149_, 0);
v_vs_201_ = lean_ctor_get(v_x_149_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_x_149_);
if (v_isSharedCheck_221_ == 0)
{
v___x_203_ = v_x_149_;
v_isShared_204_ = v_isSharedCheck_221_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_vs_201_);
lean_inc(v_ks_200_);
lean_dec(v_x_149_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_221_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_ks_200_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_vs_201_);
v___x_206_ = v_reuseFailAlloc_220_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v_newNode_207_; uint8_t v___y_209_; size_t v___x_215_; uint8_t v___x_216_; 
v_newNode_207_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v___x_206_, v_x_152_, v_x_153_);
v___x_215_ = ((size_t)7ULL);
v___x_216_ = lean_usize_dec_le(v___x_215_, v_x_151_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_217_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_207_);
v___x_218_ = lean_unsigned_to_nat(4u);
v___x_219_ = lean_nat_dec_lt(v___x_217_, v___x_218_);
lean_dec(v___x_217_);
v___y_209_ = v___x_219_;
goto v___jp_208_;
}
else
{
v___y_209_ = v___x_216_;
goto v___jp_208_;
}
v___jp_208_:
{
if (v___y_209_ == 0)
{
lean_object* v_ks_210_; lean_object* v_vs_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_ks_210_ = lean_ctor_get(v_newNode_207_, 0);
lean_inc_ref(v_ks_210_);
v_vs_211_ = lean_ctor_get(v_newNode_207_, 1);
lean_inc_ref(v_vs_211_);
lean_dec_ref(v_newNode_207_);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2);
v___x_214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_x_151_, v_ks_210_, v_vs_211_, v___x_212_, v___x_213_);
lean_dec_ref(v_vs_211_);
lean_dec_ref(v_ks_210_);
return v___x_214_;
}
else
{
return v_newNode_207_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t v_depth_222_, lean_object* v_keys_223_, lean_object* v_vals_224_, lean_object* v_i_225_, lean_object* v_entries_226_){
_start:
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = lean_array_get_size(v_keys_223_);
v___x_228_ = lean_nat_dec_lt(v_i_225_, v___x_227_);
if (v___x_228_ == 0)
{
lean_dec(v_i_225_);
return v_entries_226_;
}
else
{
lean_object* v_k_229_; lean_object* v_v_230_; uint64_t v___x_231_; size_t v_h_232_; size_t v___x_233_; lean_object* v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v_h_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_k_229_ = lean_array_fget_borrowed(v_keys_223_, v_i_225_);
v_v_230_ = lean_array_fget_borrowed(v_vals_224_, v_i_225_);
v___x_231_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_k_229_);
v_h_232_ = lean_uint64_to_usize(v___x_231_);
v___x_233_ = ((size_t)5ULL);
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_sub(v_depth_222_, v___x_235_);
v___x_237_ = lean_usize_mul(v___x_233_, v___x_236_);
v_h_238_ = lean_usize_shift_right(v_h_232_, v___x_237_);
v___x_239_ = lean_nat_add(v_i_225_, v___x_234_);
lean_dec(v_i_225_);
lean_inc(v_v_230_);
lean_inc(v_k_229_);
v___x_240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_entries_226_, v_h_238_, v_depth_222_, v_k_229_, v_v_230_);
v_i_225_ = v___x_239_;
v_entries_226_ = v___x_240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_242_, lean_object* v_keys_243_, lean_object* v_vals_244_, lean_object* v_i_245_, lean_object* v_entries_246_){
_start:
{
size_t v_depth_boxed_247_; lean_object* v_res_248_; 
v_depth_boxed_247_ = lean_unbox_usize(v_depth_242_);
lean_dec(v_depth_242_);
v_res_248_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_boxed_247_, v_keys_243_, v_vals_244_, v_i_245_, v_entries_246_);
lean_dec_ref(v_vals_244_);
lean_dec_ref(v_keys_243_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
size_t v_x_6210__boxed_254_; size_t v_x_6211__boxed_255_; lean_object* v_res_256_; 
v_x_6210__boxed_254_ = lean_unbox_usize(v_x_250_);
lean_dec(v_x_250_);
v_x_6211__boxed_255_ = lean_unbox_usize(v_x_251_);
lean_dec(v_x_251_);
v_res_256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_249_, v_x_6210__boxed_254_, v_x_6211__boxed_255_, v_x_252_, v_x_253_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
uint64_t v___x_260_; size_t v___x_261_; size_t v___x_262_; lean_object* v___x_263_; 
v___x_260_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_258_);
v___x_261_ = lean_uint64_to_usize(v___x_260_);
v___x_262_ = ((size_t)1ULL);
v___x_263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_257_, v___x_261_, v___x_262_, v_x_258_, v_x_259_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object* v_a_264_, lean_object* v_levelParams_265_, lean_object* v___x_266_, lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_a_264_);
lean_ctor_set(v___x_268_, 1, v_levelParams_265_);
v___x_269_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_267_, v___x_266_, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(lean_object* v_msgData_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_276_; lean_object* v_env_277_; lean_object* v___x_278_; lean_object* v_mctx_279_; lean_object* v_lctx_280_; lean_object* v_options_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_276_ = lean_st_ref_get(v___y_274_);
v_env_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc_ref(v_env_277_);
lean_dec(v___x_276_);
v___x_278_ = lean_st_ref_get(v___y_272_);
v_mctx_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc_ref(v_mctx_279_);
lean_dec(v___x_278_);
v_lctx_280_ = lean_ctor_get(v___y_271_, 2);
v_options_281_ = lean_ctor_get(v___y_273_, 2);
lean_inc_ref(v_options_281_);
lean_inc_ref(v_lctx_280_);
v___x_282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_282_, 0, v_env_277_);
lean_ctor_set(v___x_282_, 1, v_mctx_279_);
lean_ctor_set(v___x_282_, 2, v_lctx_280_);
lean_ctor_set(v___x_282_, 3, v_options_281_);
v___x_283_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_msgData_270_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_msgData_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msgData_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(lean_object* v_msg_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_ref_298_; lean_object* v___x_299_; lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_308_; 
v_ref_298_ = lean_ctor_get(v___y_295_, 5);
v___x_299_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msg_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_308_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
lean_inc(v_ref_298_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_ref_298_);
lean_ctor_set(v___x_304_, 1, v_a_300_);
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 1);
lean_ctor_set(v___x_302_, 0, v___x_304_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_msg_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_315_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0));
v___x_318_ = l_Lean_stringToMessageData(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2));
v___x_321_ = l_Lean_stringToMessageData(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4));
v___x_324_ = l_Lean_stringToMessageData(v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6));
v___x_327_ = l_Lean_stringToMessageData(v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8));
v___x_330_ = l_Lean_stringToMessageData(v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(lean_object* v_attrName_331_, lean_object* v_declName_332_, lean_object* v_asyncPrefix_x3f_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___y_340_; 
if (lean_obj_tag(v_asyncPrefix_x3f_333_) == 0)
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_MessageData_nil;
v___y_340_ = v___x_353_;
goto v___jp_339_;
}
else
{
lean_object* v_val_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_val_354_ = lean_ctor_get(v_asyncPrefix_x3f_333_, 0);
lean_inc(v_val_354_);
lean_dec_ref(v_asyncPrefix_x3f_333_);
v___x_355_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7);
v___x_356_ = l_Lean_MessageData_ofName(v_val_354_);
v___x_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___y_340_ = v___x_359_;
goto v___jp_339_;
}
v___jp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_341_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_342_ = l_Lean_MessageData_ofName(v_attrName_331_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = 0;
v___x_347_ = l_Lean_MessageData_ofConstName(v_declName_332_, v___x_346_);
v___x_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_345_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5);
v___x_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___y_340_);
v___x_352_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_351_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object* v_attrName_360_, lean_object* v_declName_361_, lean_object* v_asyncPrefix_x3f_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_360_, v_declName_361_, v_asyncPrefix_x3f_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_368_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(lean_object* v_attrName_372_, lean_object* v_declName_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_379_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_380_ = l_Lean_MessageData_ofName(v_attrName_372_);
v___x_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = 0;
v___x_385_ = l_Lean_MessageData_ofConstName(v_declName_373_, v___x_384_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_383_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_388_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___boxed(lean_object* v_attrName_390_, lean_object* v_declName_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_390_, v_declName_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_398_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_404_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
lean_ctor_set(v___x_404_, 2, v___x_403_);
lean_ctor_set(v___x_404_, 3, v___x_403_);
lean_ctor_set(v___x_404_, 4, v___x_403_);
lean_ctor_set(v___x_404_, 5, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object* v_attr_405_, lean_object* v_decl_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___x_456_; lean_object* v_env_457_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___x_472_; 
v___x_456_ = lean_st_ref_get(v___y_410_);
v_env_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc_ref(v_env_457_);
lean_dec(v___x_456_);
v___x_472_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_457_, v_decl_406_);
if (lean_obj_tag(v___x_472_) == 0)
{
v___y_459_ = v___y_407_;
v___y_460_ = v___y_408_;
v___y_461_ = v___y_409_;
v___y_462_ = v___y_410_;
goto v___jp_458_;
}
else
{
lean_object* v_attr_473_; lean_object* v_toAttributeImplCore_474_; lean_object* v_name_475_; lean_object* v___x_476_; 
lean_dec_ref(v___x_472_);
lean_dec_ref(v_env_457_);
v_attr_473_ = lean_ctor_get(v_attr_405_, 0);
lean_inc_ref(v_attr_473_);
lean_dec_ref(v_attr_405_);
v_toAttributeImplCore_474_ = lean_ctor_get(v_attr_473_, 0);
lean_inc_ref(v_toAttributeImplCore_474_);
lean_dec_ref(v_attr_473_);
v_name_475_ = lean_ctor_get(v_toAttributeImplCore_474_, 1);
lean_inc(v_name_475_);
lean_dec_ref(v_toAttributeImplCore_474_);
v___x_476_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_name_475_, v_decl_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v___x_476_;
}
v___jp_412_:
{
lean_object* v___x_415_; lean_object* v_ext_416_; lean_object* v_toEnvExtension_417_; lean_object* v_env_418_; lean_object* v_nextMacroScope_419_; lean_object* v_ngen_420_; lean_object* v_auxDeclNGen_421_; lean_object* v_traceState_422_; lean_object* v_messages_423_; lean_object* v_infoState_424_; lean_object* v_snapshotTasks_425_; lean_object* v_newDecls_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_454_; 
v___x_415_ = lean_st_ref_take(v___y_414_);
v_ext_416_ = lean_ctor_get(v_attr_405_, 1);
lean_inc_ref(v_ext_416_);
lean_dec_ref(v_attr_405_);
v_toEnvExtension_417_ = lean_ctor_get(v_ext_416_, 0);
v_env_418_ = lean_ctor_get(v___x_415_, 0);
v_nextMacroScope_419_ = lean_ctor_get(v___x_415_, 1);
v_ngen_420_ = lean_ctor_get(v___x_415_, 2);
v_auxDeclNGen_421_ = lean_ctor_get(v___x_415_, 3);
v_traceState_422_ = lean_ctor_get(v___x_415_, 4);
v_messages_423_ = lean_ctor_get(v___x_415_, 6);
v_infoState_424_ = lean_ctor_get(v___x_415_, 7);
v_snapshotTasks_425_ = lean_ctor_get(v___x_415_, 8);
v_newDecls_426_ = lean_ctor_get(v___x_415_, 9);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v___x_415_, 5);
lean_dec(v_unused_455_);
v___x_428_ = v___x_415_;
v_isShared_429_ = v_isSharedCheck_454_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_newDecls_426_);
lean_inc(v_snapshotTasks_425_);
lean_inc(v_infoState_424_);
lean_inc(v_messages_423_);
lean_inc(v_traceState_422_);
lean_inc(v_auxDeclNGen_421_);
lean_inc(v_ngen_420_);
lean_inc(v_nextMacroScope_419_);
lean_inc(v_env_418_);
lean_dec(v___x_415_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_454_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_asyncMode_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v_asyncMode_430_ = lean_ctor_get(v_toEnvExtension_417_, 2);
lean_inc(v_asyncMode_430_);
lean_inc(v_decl_406_);
v___x_431_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_416_, v_env_418_, v_decl_406_, v_asyncMode_430_, v_decl_406_);
lean_dec(v_asyncMode_430_);
v___x_432_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 5, v___x_432_);
lean_ctor_set(v___x_428_, 0, v___x_431_);
v___x_434_ = v___x_428_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_nextMacroScope_419_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_ngen_420_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_auxDeclNGen_421_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_traceState_422_);
lean_ctor_set(v_reuseFailAlloc_453_, 5, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_453_, 6, v_messages_423_);
lean_ctor_set(v_reuseFailAlloc_453_, 7, v_infoState_424_);
lean_ctor_set(v_reuseFailAlloc_453_, 8, v_snapshotTasks_425_);
lean_ctor_set(v_reuseFailAlloc_453_, 9, v_newDecls_426_);
v___x_434_ = v_reuseFailAlloc_453_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_mctx_437_; lean_object* v_zetaDeltaFVarIds_438_; lean_object* v_postponed_439_; lean_object* v_diag_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_451_; 
v___x_435_ = lean_st_ref_set(v___y_414_, v___x_434_);
v___x_436_ = lean_st_ref_take(v___y_413_);
v_mctx_437_ = lean_ctor_get(v___x_436_, 0);
v_zetaDeltaFVarIds_438_ = lean_ctor_get(v___x_436_, 2);
v_postponed_439_ = lean_ctor_get(v___x_436_, 3);
v_diag_440_ = lean_ctor_get(v___x_436_, 4);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v___x_436_, 1);
lean_dec(v_unused_452_);
v___x_442_ = v___x_436_;
v_isShared_443_ = v_isSharedCheck_451_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_diag_440_);
lean_inc(v_postponed_439_);
lean_inc(v_zetaDeltaFVarIds_438_);
lean_inc(v_mctx_437_);
lean_dec(v___x_436_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_451_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_mctx_437_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_zetaDeltaFVarIds_438_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v_postponed_439_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v_diag_440_);
v___x_446_ = v_reuseFailAlloc_450_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_st_ref_set(v___y_413_, v___x_446_);
v___x_448_ = lean_box(0);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
}
}
}
v___jp_458_:
{
lean_object* v_ext_463_; lean_object* v_toEnvExtension_464_; lean_object* v_attr_465_; lean_object* v_asyncMode_466_; uint8_t v___x_467_; 
v_ext_463_ = lean_ctor_get(v_attr_405_, 1);
v_toEnvExtension_464_ = lean_ctor_get(v_ext_463_, 0);
v_attr_465_ = lean_ctor_get(v_attr_405_, 0);
v_asyncMode_466_ = lean_ctor_get(v_toEnvExtension_464_, 2);
lean_inc(v_decl_406_);
lean_inc_ref(v_env_457_);
v___x_467_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_457_, v_decl_406_, v_asyncMode_466_);
if (v___x_467_ == 0)
{
lean_object* v_toAttributeImplCore_468_; lean_object* v_name_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc_ref(v_attr_465_);
lean_dec_ref(v_attr_405_);
v_toAttributeImplCore_468_ = lean_ctor_get(v_attr_465_, 0);
lean_inc_ref(v_toAttributeImplCore_468_);
lean_dec_ref(v_attr_465_);
v_name_469_ = lean_ctor_get(v_toAttributeImplCore_468_, 1);
lean_inc(v_name_469_);
lean_dec_ref(v_toAttributeImplCore_468_);
v___x_470_ = l_Lean_Environment_asyncPrefix_x3f(v_env_457_);
v___x_471_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_name_469_, v_decl_406_, v___x_470_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
return v___x_471_;
}
else
{
lean_dec_ref(v_env_457_);
v___y_413_ = v___y_460_;
v___y_414_ = v___y_462_;
goto v___jp_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object* v_attr_477_, lean_object* v_decl_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v_attr_477_, v_decl_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(lean_object* v_keys_485_, lean_object* v_vals_486_, lean_object* v_i_487_, lean_object* v_k_488_){
_start:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_array_get_size(v_keys_485_);
v___x_490_ = lean_nat_dec_lt(v_i_487_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec(v_i_487_);
v___x_491_ = lean_box(0);
return v___x_491_;
}
else
{
lean_object* v_k_x27_492_; uint8_t v___x_493_; 
v_k_x27_492_ = lean_array_fget_borrowed(v_keys_485_, v_i_487_);
v___x_493_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_k_488_, v_k_x27_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_add(v_i_487_, v___x_494_);
lean_dec(v_i_487_);
v_i_487_ = v___x_495_;
goto _start;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_array_fget_borrowed(v_vals_486_, v_i_487_);
lean_dec(v_i_487_);
lean_inc(v___x_497_);
v___x_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_keys_499_, lean_object* v_vals_500_, lean_object* v_i_501_, lean_object* v_k_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_499_, v_vals_500_, v_i_501_, v_k_502_);
lean_dec_ref(v_k_502_);
lean_dec_ref(v_vals_500_);
lean_dec_ref(v_keys_499_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(lean_object* v_x_504_, size_t v_x_505_, lean_object* v_x_506_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
lean_object* v_es_507_; lean_object* v___x_508_; size_t v___x_509_; size_t v___x_510_; size_t v___x_511_; lean_object* v_j_512_; lean_object* v___x_513_; 
v_es_507_ = lean_ctor_get(v_x_504_, 0);
v___x_508_ = lean_box(2);
v___x_509_ = ((size_t)5ULL);
v___x_510_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1);
v___x_511_ = lean_usize_land(v_x_505_, v___x_510_);
v_j_512_ = lean_usize_to_nat(v___x_511_);
v___x_513_ = lean_array_get_borrowed(v___x_508_, v_es_507_, v_j_512_);
lean_dec(v_j_512_);
switch(lean_obj_tag(v___x_513_))
{
case 0:
{
lean_object* v_key_514_; lean_object* v_val_515_; uint8_t v___x_516_; 
v_key_514_ = lean_ctor_get(v___x_513_, 0);
v_val_515_ = lean_ctor_get(v___x_513_, 1);
v___x_516_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_506_, v_key_514_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
v___x_517_ = lean_box(0);
return v___x_517_;
}
else
{
lean_object* v___x_518_; 
lean_inc(v_val_515_);
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v_val_515_);
return v___x_518_;
}
}
case 1:
{
lean_object* v_node_519_; size_t v___x_520_; 
v_node_519_ = lean_ctor_get(v___x_513_, 0);
v___x_520_ = lean_usize_shift_right(v_x_505_, v___x_509_);
v_x_504_ = v_node_519_;
v_x_505_ = v___x_520_;
goto _start;
}
default: 
{
lean_object* v___x_522_; 
v___x_522_ = lean_box(0);
return v___x_522_;
}
}
}
else
{
lean_object* v_ks_523_; lean_object* v_vs_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_ks_523_ = lean_ctor_get(v_x_504_, 0);
v_vs_524_ = lean_ctor_get(v_x_504_, 1);
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_ks_523_, v_vs_524_, v___x_525_, v_x_506_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
size_t v_x_6765__boxed_530_; lean_object* v_res_531_; 
v_x_6765__boxed_530_ = lean_unbox_usize(v_x_528_);
lean_dec(v_x_528_);
v_res_531_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_527_, v_x_6765__boxed_530_, v_x_529_);
lean_dec_ref(v_x_529_);
lean_dec_ref(v_x_527_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
uint64_t v___x_534_; size_t v___x_535_; lean_object* v___x_536_; 
v___x_534_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_533_);
v___x_535_ = lean_uint64_to_usize(v___x_534_);
v___x_536_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_532_, v___x_535_, v_x_533_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg___boxed(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_537_, v_x_538_);
lean_dec_ref(v_x_538_);
lean_dec_ref(v_x_537_);
return v_res_539_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
if (lean_obj_tag(v_x_541_) == 0)
{
uint8_t v___x_542_; 
v___x_542_ = 1;
return v___x_542_;
}
else
{
uint8_t v___x_543_; 
v___x_543_ = 0;
return v___x_543_;
}
}
else
{
if (lean_obj_tag(v_x_541_) == 0)
{
uint8_t v___x_544_; 
v___x_544_ = 0;
return v___x_544_;
}
else
{
lean_object* v_head_545_; lean_object* v_tail_546_; lean_object* v_head_547_; lean_object* v_tail_548_; uint8_t v___x_549_; 
v_head_545_ = lean_ctor_get(v_x_540_, 0);
v_tail_546_ = lean_ctor_get(v_x_540_, 1);
v_head_547_ = lean_ctor_get(v_x_541_, 0);
v_tail_548_ = lean_ctor_get(v_x_541_, 1);
v___x_549_ = lean_name_eq(v_head_545_, v_head_547_);
if (v___x_549_ == 0)
{
return v___x_549_;
}
else
{
v_x_540_ = v_tail_546_;
v_x_541_ = v_tail_548_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_x_551_, v_x_552_);
lean_dec(v_x_552_);
lean_dec(v_x_551_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object* v_levelParams_558_, lean_object* v_type_559_, lean_object* v_value_560_, lean_object* v_kind_x3f_561_, uint8_t v_cache_562_, uint8_t v_inferRfl_563_, uint8_t v_forceExpose_564_, uint8_t v_defeq_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; lean_object* v_env_572_; lean_object* v___x_573_; lean_object* v_asyncMode_574_; uint8_t v_isExporting_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; uint8_t v___y_670_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_777_; lean_object* v___y_778_; uint8_t v___y_779_; lean_object* v___x_792_; lean_object* v___y_794_; uint8_t v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; uint8_t v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; uint8_t v___y_837_; 
v___x_571_ = lean_st_ref_get(v_a_569_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref_n(v_env_572_, 2);
lean_dec(v___x_571_);
v___x_573_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_574_ = lean_ctor_get(v___x_573_, 2);
v_isExporting_575_ = lean_ctor_get_uint8(v_env_572_, sizeof(void*)*8);
v___x_576_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_577_ = lean_box(0);
v___x_792_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_576_, v___x_573_, v_env_572_, v_asyncMode_574_, v___x_577_);
if (v_isExporting_575_ == 0)
{
uint8_t v___x_841_; 
v___x_841_ = 1;
v___y_837_ = v___x_841_;
goto v___jp_836_;
}
else
{
uint8_t v___x_842_; 
v___x_842_ = 0;
v___y_837_ = v___x_842_;
goto v___jp_836_;
}
v___jp_578_:
{
lean_object* v___x_583_; lean_object* v_env_584_; lean_object* v_nextMacroScope_585_; lean_object* v_ngen_586_; lean_object* v_auxDeclNGen_587_; lean_object* v_traceState_588_; lean_object* v_messages_589_; lean_object* v_infoState_590_; lean_object* v_snapshotTasks_591_; lean_object* v_newDecls_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_618_; 
v___x_583_ = lean_st_ref_take(v___y_582_);
v_env_584_ = lean_ctor_get(v___x_583_, 0);
v_nextMacroScope_585_ = lean_ctor_get(v___x_583_, 1);
v_ngen_586_ = lean_ctor_get(v___x_583_, 2);
v_auxDeclNGen_587_ = lean_ctor_get(v___x_583_, 3);
v_traceState_588_ = lean_ctor_get(v___x_583_, 4);
v_messages_589_ = lean_ctor_get(v___x_583_, 6);
v_infoState_590_ = lean_ctor_get(v___x_583_, 7);
v_snapshotTasks_591_ = lean_ctor_get(v___x_583_, 8);
v_newDecls_592_ = lean_ctor_get(v___x_583_, 9);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v___x_583_, 5);
lean_dec(v_unused_619_);
v___x_594_ = v___x_583_;
v_isShared_595_ = v_isSharedCheck_618_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_newDecls_592_);
lean_inc(v_snapshotTasks_591_);
lean_inc(v_infoState_590_);
lean_inc(v_messages_589_);
lean_inc(v_traceState_588_);
lean_inc(v_auxDeclNGen_587_);
lean_inc(v_ngen_586_);
lean_inc(v_nextMacroScope_585_);
lean_inc(v_env_584_);
lean_dec(v___x_583_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_618_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_596_ = l_Lean_EnvExtension_modifyState___redArg(v___x_573_, v_env_584_, v___y_579_, v_asyncMode_574_, v___x_577_);
v___x_597_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 5, v___x_597_);
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_599_ = v___x_594_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_nextMacroScope_585_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_ngen_586_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_auxDeclNGen_587_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_traceState_588_);
lean_ctor_set(v_reuseFailAlloc_617_, 5, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_617_, 6, v_messages_589_);
lean_ctor_set(v_reuseFailAlloc_617_, 7, v_infoState_590_);
lean_ctor_set(v_reuseFailAlloc_617_, 8, v_snapshotTasks_591_);
lean_ctor_set(v_reuseFailAlloc_617_, 9, v_newDecls_592_);
v___x_599_ = v_reuseFailAlloc_617_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_mctx_602_; lean_object* v_zetaDeltaFVarIds_603_; lean_object* v_postponed_604_; lean_object* v_diag_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_615_; 
v___x_600_ = lean_st_ref_set(v___y_582_, v___x_599_);
v___x_601_ = lean_st_ref_take(v___y_581_);
v_mctx_602_ = lean_ctor_get(v___x_601_, 0);
v_zetaDeltaFVarIds_603_ = lean_ctor_get(v___x_601_, 2);
v_postponed_604_ = lean_ctor_get(v___x_601_, 3);
v_diag_605_ = lean_ctor_get(v___x_601_, 4);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_601_, 1);
lean_dec(v_unused_616_);
v___x_607_ = v___x_601_;
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_diag_605_);
lean_inc(v_postponed_604_);
lean_inc(v_zetaDeltaFVarIds_603_);
lean_inc(v_mctx_602_);
lean_dec(v___x_601_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_mctx_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_zetaDeltaFVarIds_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_postponed_604_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_diag_605_);
v___x_611_ = v_reuseFailAlloc_614_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_st_ref_set(v___y_581_, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___y_580_);
return v___x_613_;
}
}
}
}
}
v___jp_620_:
{
if (v_inferRfl_563_ == 0)
{
v___y_579_ = v___y_621_;
v___y_580_ = v___y_622_;
v___y_581_ = v___y_624_;
v___y_582_ = v___y_626_;
goto v___jp_578_;
}
else
{
lean_object* v___x_627_; 
lean_inc(v___y_622_);
v___x_627_ = l_Lean_inferDefEqAttr(v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec_ref(v___x_627_);
v___y_579_ = v___y_621_;
v___y_580_ = v___y_622_;
v___y_581_ = v___y_624_;
v___y_582_ = v___y_626_;
goto v___jp_578_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
v___jp_636_:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_addDecl(v___y_643_, v_forceExpose_564_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_dec_ref(v___x_644_);
if (v_defeq_565_ == 0)
{
v___y_621_ = v___y_639_;
v___y_622_ = v___y_640_;
v___y_623_ = v___y_637_;
v___y_624_ = v___y_638_;
v___y_625_ = v___y_641_;
v___y_626_ = v___y_642_;
goto v___jp_620_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = l_Lean_defeqAttr;
lean_inc(v___y_640_);
v___x_646_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_645_, v___y_640_, v___y_637_, v___y_638_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_dec_ref(v___x_646_);
v___y_621_ = v___y_639_;
v___y_622_ = v___y_640_;
v___y_623_ = v___y_637_;
v___y_624_ = v___y_638_;
v___y_625_ = v___y_641_;
v___y_626_ = v___y_642_;
goto v___jp_620_;
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
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
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
v_a_655_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_644_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_644_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
v___jp_663_:
{
if (v___y_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_inc_n(v___y_667_, 2);
v___x_671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_671_, 0, v___y_667_);
lean_ctor_set(v___x_671_, 1, v_levelParams_558_);
lean_ctor_set(v___x_671_, 2, v_type_559_);
v___x_672_ = lean_box(0);
v___x_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_673_, 0, v___y_667_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_674_, 0, v___x_671_);
lean_ctor_set(v___x_674_, 1, v_value_560_);
lean_ctor_set(v___x_674_, 2, v___x_673_);
v___x_675_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
v___y_637_ = v___y_664_;
v___y_638_ = v___y_665_;
v___y_639_ = v___y_666_;
v___y_640_ = v___y_667_;
v___y_641_ = v___y_668_;
v___y_642_ = v___y_669_;
v___y_643_ = v___x_675_;
goto v___jp_636_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_inc_n(v___y_667_, 2);
v___x_676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_676_, 0, v___y_667_);
lean_ctor_set(v___x_676_, 1, v_levelParams_558_);
lean_ctor_set(v___x_676_, 2, v_type_559_);
v___x_677_ = lean_box(0);
v___x_678_ = 0;
v___x_679_ = lean_box(0);
v___x_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_680_, 0, v___y_667_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_681_, 0, v___x_676_);
lean_ctor_set(v___x_681_, 1, v_value_560_);
lean_ctor_set(v___x_681_, 2, v___x_677_);
lean_ctor_set(v___x_681_, 3, v___x_680_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*4, v___x_678_);
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
v___y_637_ = v___y_664_;
v___y_638_ = v___y_665_;
v___y_639_ = v___y_666_;
v___y_640_ = v___y_667_;
v___y_641_ = v___y_668_;
v___y_642_ = v___y_669_;
v___y_643_ = v___x_682_;
goto v___jp_636_;
}
}
v___jp_683_:
{
lean_object* v___x_690_; lean_object* v_a_691_; lean_object* v___f_692_; uint8_t v___x_693_; 
v___x_690_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_685_, v___y_689_);
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_n(v_a_691_, 2);
lean_dec_ref(v___x_690_);
lean_inc(v_levelParams_558_);
v___f_692_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_692_, 0, v_a_691_);
lean_closure_set(v___f_692_, 1, v_levelParams_558_);
lean_closure_set(v___f_692_, 2, v___y_684_);
lean_inc_ref(v_env_572_);
v___x_693_ = l_Lean_Environment_hasUnsafe(v_env_572_, v_type_559_);
if (v___x_693_ == 0)
{
uint8_t v___x_694_; 
v___x_694_ = l_Lean_Environment_hasUnsafe(v_env_572_, v_value_560_);
v___y_664_ = v___y_686_;
v___y_665_ = v___y_687_;
v___y_666_ = v___f_692_;
v___y_667_ = v_a_691_;
v___y_668_ = v___y_688_;
v___y_669_ = v___y_689_;
v___y_670_ = v___x_694_;
goto v___jp_663_;
}
else
{
lean_dec_ref(v_env_572_);
v___y_664_ = v___y_686_;
v___y_665_ = v___y_687_;
v___y_666_ = v___f_692_;
v___y_667_ = v_a_691_;
v___y_668_ = v___y_688_;
v___y_669_ = v___y_689_;
v___y_670_ = v___x_693_;
goto v___jp_663_;
}
}
v___jp_695_:
{
lean_object* v___x_700_; lean_object* v_env_701_; lean_object* v_nextMacroScope_702_; lean_object* v_ngen_703_; lean_object* v_auxDeclNGen_704_; lean_object* v_traceState_705_; lean_object* v_messages_706_; lean_object* v_infoState_707_; lean_object* v_snapshotTasks_708_; lean_object* v_newDecls_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_735_; 
v___x_700_ = lean_st_ref_take(v___y_699_);
v_env_701_ = lean_ctor_get(v___x_700_, 0);
v_nextMacroScope_702_ = lean_ctor_get(v___x_700_, 1);
v_ngen_703_ = lean_ctor_get(v___x_700_, 2);
v_auxDeclNGen_704_ = lean_ctor_get(v___x_700_, 3);
v_traceState_705_ = lean_ctor_get(v___x_700_, 4);
v_messages_706_ = lean_ctor_get(v___x_700_, 6);
v_infoState_707_ = lean_ctor_get(v___x_700_, 7);
v_snapshotTasks_708_ = lean_ctor_get(v___x_700_, 8);
v_newDecls_709_ = lean_ctor_get(v___x_700_, 9);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v___x_700_, 5);
lean_dec(v_unused_736_);
v___x_711_ = v___x_700_;
v_isShared_712_ = v_isSharedCheck_735_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_newDecls_709_);
lean_inc(v_snapshotTasks_708_);
lean_inc(v_infoState_707_);
lean_inc(v_messages_706_);
lean_inc(v_traceState_705_);
lean_inc(v_auxDeclNGen_704_);
lean_inc(v_ngen_703_);
lean_inc(v_nextMacroScope_702_);
lean_inc(v_env_701_);
lean_dec(v___x_700_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_735_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = l_Lean_EnvExtension_modifyState___redArg(v___x_573_, v_env_701_, v___y_697_, v_asyncMode_574_, v___x_577_);
v___x_714_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 5, v___x_714_);
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_nextMacroScope_702_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_ngen_703_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_auxDeclNGen_704_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_traceState_705_);
lean_ctor_set(v_reuseFailAlloc_734_, 5, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_734_, 6, v_messages_706_);
lean_ctor_set(v_reuseFailAlloc_734_, 7, v_infoState_707_);
lean_ctor_set(v_reuseFailAlloc_734_, 8, v_snapshotTasks_708_);
lean_ctor_set(v_reuseFailAlloc_734_, 9, v_newDecls_709_);
v___x_716_ = v_reuseFailAlloc_734_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_mctx_719_; lean_object* v_zetaDeltaFVarIds_720_; lean_object* v_postponed_721_; lean_object* v_diag_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_732_; 
v___x_717_ = lean_st_ref_set(v___y_699_, v___x_716_);
v___x_718_ = lean_st_ref_take(v___y_698_);
v_mctx_719_ = lean_ctor_get(v___x_718_, 0);
v_zetaDeltaFVarIds_720_ = lean_ctor_get(v___x_718_, 2);
v_postponed_721_ = lean_ctor_get(v___x_718_, 3);
v_diag_722_ = lean_ctor_get(v___x_718_, 4);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v___x_718_, 1);
lean_dec(v_unused_733_);
v___x_724_ = v___x_718_;
v_isShared_725_ = v_isSharedCheck_732_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_diag_722_);
lean_inc(v_postponed_721_);
lean_inc(v_zetaDeltaFVarIds_720_);
lean_inc(v_mctx_719_);
lean_dec(v___x_718_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_732_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__3);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v___x_726_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_mctx_719_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_zetaDeltaFVarIds_720_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_postponed_721_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v_diag_722_);
v___x_728_ = v_reuseFailAlloc_731_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_st_ref_set(v___y_698_, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___y_696_);
return v___x_730_;
}
}
}
}
}
v___jp_737_:
{
if (v_inferRfl_563_ == 0)
{
v___y_696_ = v___y_738_;
v___y_697_ = v___y_739_;
v___y_698_ = v___y_741_;
v___y_699_ = v___y_743_;
goto v___jp_695_;
}
else
{
lean_object* v___x_744_; 
lean_inc(v___y_738_);
v___x_744_ = l_Lean_inferDefEqAttr(v___y_738_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_dec_ref(v___x_744_);
v___y_696_ = v___y_738_;
v___y_697_ = v___y_739_;
v___y_698_ = v___y_741_;
v___y_699_ = v___y_743_;
goto v___jp_695_;
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
lean_object* v___x_757_; 
v___x_757_ = l_Lean_addDecl(v___y_756_, v_forceExpose_564_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_dec_ref(v___x_757_);
if (v_defeq_565_ == 0)
{
v___y_738_ = v___y_754_;
v___y_739_ = v___y_755_;
v___y_740_ = v_a_566_;
v___y_741_ = v_a_567_;
v___y_742_ = v_a_568_;
v___y_743_ = v_a_569_;
goto v___jp_737_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = l_Lean_defeqAttr;
lean_inc(v___y_754_);
v___x_759_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_758_, v___y_754_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_dec_ref(v___x_759_);
v___y_738_ = v___y_754_;
v___y_739_ = v___y_755_;
v___y_740_ = v_a_566_;
v___y_741_ = v_a_567_;
v___y_742_ = v_a_568_;
v___y_743_ = v_a_569_;
goto v___jp_737_;
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
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
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
v_a_768_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_757_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_757_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
v___jp_776_:
{
if (v___y_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_inc_n(v___y_777_, 2);
v___x_780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_780_, 0, v___y_777_);
lean_ctor_set(v___x_780_, 1, v_levelParams_558_);
lean_ctor_set(v___x_780_, 2, v_type_559_);
v___x_781_ = lean_box(0);
v___x_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_782_, 0, v___y_777_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_783_, 0, v___x_780_);
lean_ctor_set(v___x_783_, 1, v_value_560_);
lean_ctor_set(v___x_783_, 2, v___x_782_);
v___x_784_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
v___y_754_ = v___y_777_;
v___y_755_ = v___y_778_;
v___y_756_ = v___x_784_;
goto v___jp_753_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_inc_n(v___y_777_, 2);
v___x_785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_785_, 0, v___y_777_);
lean_ctor_set(v___x_785_, 1, v_levelParams_558_);
lean_ctor_set(v___x_785_, 2, v_type_559_);
v___x_786_ = lean_box(0);
v___x_787_ = 0;
v___x_788_ = lean_box(0);
v___x_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_789_, 0, v___y_777_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_790_, 0, v___x_785_);
lean_ctor_set(v___x_790_, 1, v_value_560_);
lean_ctor_set(v___x_790_, 2, v___x_786_);
lean_ctor_set(v___x_790_, 3, v___x_789_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*4, v___x_787_);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
v___y_754_ = v___y_777_;
v___y_755_ = v___y_778_;
v___y_756_ = v___x_791_;
goto v___jp_753_;
}
}
v___jp_793_:
{
if (v___y_795_ == 0)
{
lean_dec(v___x_792_);
v___y_684_ = v___y_794_;
v___y_685_ = v___y_796_;
v___y_686_ = v___y_797_;
v___y_687_ = v___y_798_;
v___y_688_ = v___y_799_;
v___y_689_ = v___y_800_;
goto v___jp_683_;
}
else
{
uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = 0;
lean_inc_ref(v_type_559_);
v___x_802_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_802_, 0, v_type_559_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*1, v___x_801_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*1 + 1, v_defeq_565_);
v___x_803_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_792_, v___x_802_);
lean_dec_ref(v___x_802_);
lean_dec(v___x_792_);
if (lean_obj_tag(v___x_803_) == 1)
{
lean_object* v_val_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_814_; 
v_val_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_814_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_val_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_fst_808_; lean_object* v_snd_809_; uint8_t v___x_810_; 
v_fst_808_ = lean_ctor_get(v_val_804_, 0);
lean_inc(v_fst_808_);
v_snd_809_ = lean_ctor_get(v_val_804_, 1);
lean_inc(v_snd_809_);
lean_dec(v_val_804_);
v___x_810_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_558_, v_snd_809_);
lean_dec(v_snd_809_);
if (v___x_810_ == 0)
{
lean_dec(v_fst_808_);
lean_del_object(v___x_806_);
v___y_684_ = v___y_794_;
v___y_685_ = v___y_796_;
v___y_686_ = v___y_797_;
v___y_687_ = v___y_798_;
v___y_688_ = v___y_799_;
v___y_689_ = v___y_800_;
goto v___jp_683_;
}
else
{
lean_object* v___x_812_; 
lean_dec(v___y_796_);
lean_dec_ref(v___y_794_);
lean_dec_ref(v_env_572_);
lean_dec_ref(v_value_560_);
lean_dec_ref(v_type_559_);
lean_dec(v_levelParams_558_);
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 0);
lean_ctor_set(v___x_806_, 0, v_fst_808_);
v___x_812_ = v___x_806_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_fst_808_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_dec(v___x_803_);
v___y_684_ = v___y_794_;
v___y_685_ = v___y_796_;
v___y_686_ = v___y_797_;
v___y_687_ = v___y_798_;
v___y_688_ = v___y_799_;
v___y_689_ = v___y_800_;
goto v___jp_683_;
}
}
}
v___jp_815_:
{
if (v_cache_562_ == 0)
{
lean_object* v___x_819_; lean_object* v_a_820_; lean_object* v___f_821_; uint8_t v___x_822_; 
lean_dec(v___x_792_);
v___x_819_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_818_, v_a_569_);
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc_n(v_a_820_, 2);
lean_dec_ref(v___x_819_);
lean_inc(v_levelParams_558_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_821_, 0, v_a_820_);
lean_closure_set(v___f_821_, 1, v_levelParams_558_);
lean_closure_set(v___f_821_, 2, v___y_817_);
lean_inc_ref(v_env_572_);
v___x_822_ = l_Lean_Environment_hasUnsafe(v_env_572_, v_type_559_);
if (v___x_822_ == 0)
{
uint8_t v___x_823_; 
v___x_823_ = l_Lean_Environment_hasUnsafe(v_env_572_, v_value_560_);
v___y_777_ = v_a_820_;
v___y_778_ = v___f_821_;
v___y_779_ = v___x_823_;
goto v___jp_776_;
}
else
{
lean_dec_ref(v_env_572_);
v___y_777_ = v_a_820_;
v___y_778_ = v___f_821_;
v___y_779_ = v___x_822_;
goto v___jp_776_;
}
}
else
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_792_, v___y_817_);
if (lean_obj_tag(v___x_824_) == 1)
{
lean_object* v_val_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_835_; 
v_val_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_835_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_835_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_val_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_835_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_fst_829_; lean_object* v_snd_830_; uint8_t v___x_831_; 
v_fst_829_ = lean_ctor_get(v_val_825_, 0);
lean_inc(v_fst_829_);
v_snd_830_ = lean_ctor_get(v_val_825_, 1);
lean_inc(v_snd_830_);
lean_dec(v_val_825_);
v___x_831_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_558_, v_snd_830_);
lean_dec(v_snd_830_);
if (v___x_831_ == 0)
{
lean_dec(v_fst_829_);
lean_del_object(v___x_827_);
v___y_794_ = v___y_817_;
v___y_795_ = v___y_816_;
v___y_796_ = v___y_818_;
v___y_797_ = v_a_566_;
v___y_798_ = v_a_567_;
v___y_799_ = v_a_568_;
v___y_800_ = v_a_569_;
goto v___jp_793_;
}
else
{
lean_object* v___x_833_; 
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___x_792_);
lean_dec_ref(v_env_572_);
lean_dec_ref(v_value_560_);
lean_dec_ref(v_type_559_);
lean_dec(v_levelParams_558_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 0);
lean_ctor_set(v___x_827_, 0, v_fst_829_);
v___x_833_ = v___x_827_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_fst_829_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_dec(v___x_824_);
v___y_794_ = v___y_817_;
v___y_795_ = v___y_816_;
v___y_796_ = v___y_818_;
v___y_797_ = v_a_566_;
v___y_798_ = v_a_567_;
v___y_799_ = v_a_568_;
v___y_800_ = v_a_569_;
goto v___jp_793_;
}
}
}
v___jp_836_:
{
lean_object* v___x_838_; 
lean_inc_ref(v_type_559_);
v___x_838_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_838_, 0, v_type_559_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*1, v___y_837_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*1 + 1, v_defeq_565_);
if (lean_obj_tag(v_kind_x3f_561_) == 0)
{
lean_object* v___x_839_; 
v___x_839_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__1));
v___y_816_ = v___y_837_;
v___y_817_ = v___x_838_;
v___y_818_ = v___x_839_;
goto v___jp_815_;
}
else
{
lean_object* v_val_840_; 
v_val_840_ = lean_ctor_get(v_kind_x3f_561_, 0);
lean_inc(v_val_840_);
lean_dec_ref(v_kind_x3f_561_);
v___y_816_ = v___y_837_;
v___y_817_ = v___x_838_;
v___y_818_ = v_val_840_;
goto v___jp_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_843_, lean_object* v_type_844_, lean_object* v_value_845_, lean_object* v_kind_x3f_846_, lean_object* v_cache_847_, lean_object* v_inferRfl_848_, lean_object* v_forceExpose_849_, lean_object* v_defeq_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
uint8_t v_cache_boxed_856_; uint8_t v_inferRfl_boxed_857_; uint8_t v_forceExpose_boxed_858_; uint8_t v_defeq_boxed_859_; lean_object* v_res_860_; 
v_cache_boxed_856_ = lean_unbox(v_cache_847_);
v_inferRfl_boxed_857_ = lean_unbox(v_inferRfl_848_);
v_forceExpose_boxed_858_ = lean_unbox(v_forceExpose_849_);
v_defeq_boxed_859_ = lean_unbox(v_defeq_850_);
v_res_860_ = l_Lean_Meta_mkAuxLemma(v_levelParams_843_, v_type_844_, v_value_845_, v_kind_x3f_846_, v_cache_boxed_856_, v_inferRfl_boxed_857_, v_forceExpose_boxed_858_, v_defeq_boxed_859_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_862_, v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_867_, v_x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(v_00_u03b2_870_, v_x_871_, v_x_872_);
lean_dec_ref(v_x_872_);
lean_dec_ref(v_x_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_874_, lean_object* v_x_875_, size_t v_x_876_, size_t v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_875_, v_x_876_, v_x_877_, v_x_878_, v_x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
size_t v_x_7402__boxed_887_; size_t v_x_7403__boxed_888_; lean_object* v_res_889_; 
v_x_7402__boxed_887_ = lean_unbox_usize(v_x_883_);
lean_dec(v_x_883_);
v_x_7403__boxed_888_ = lean_unbox_usize(v_x_884_);
lean_dec(v_x_884_);
v_res_889_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_881_, v_x_882_, v_x_7402__boxed_887_, v_x_7403__boxed_888_, v_x_885_, v_x_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b1_890_, lean_object* v_attrName_891_, lean_object* v_declName_892_, lean_object* v_asyncPrefix_x3f_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_891_, v_declName_892_, v_asyncPrefix_x3f_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_900_, lean_object* v_attrName_901_, lean_object* v_declName_902_, lean_object* v_asyncPrefix_x3f_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b1_900_, v_attrName_901_, v_declName_902_, v_asyncPrefix_x3f_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(lean_object* v_00_u03b1_910_, lean_object* v_attrName_911_, lean_object* v_declName_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_911_, v_declName_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___boxed(lean_object* v_00_u03b1_919_, lean_object* v_attrName_920_, lean_object* v_declName_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(v_00_u03b1_919_, v_attrName_920_, v_declName_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object* v_00_u03b2_928_, lean_object* v_x_929_, size_t v_x_930_, lean_object* v_x_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_929_, v_x_930_, v_x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object* v_00_u03b2_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
size_t v_x_7453__boxed_937_; lean_object* v_res_938_; 
v_x_7453__boxed_937_ = lean_unbox_usize(v_x_935_);
lean_dec(v_x_935_);
v_res_938_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(v_00_u03b2_933_, v_x_934_, v_x_7453__boxed_937_, v_x_936_);
lean_dec_ref(v_x_936_);
lean_dec_ref(v_x_934_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_939_, lean_object* v_n_940_, lean_object* v_k_941_, lean_object* v_v_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_940_, v_k_941_, v_v_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_944_, size_t v_depth_945_, lean_object* v_keys_946_, lean_object* v_vals_947_, lean_object* v_heq_948_, lean_object* v_i_949_, lean_object* v_entries_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_945_, v_keys_946_, v_vals_947_, v_i_949_, v_entries_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_952_, lean_object* v_depth_953_, lean_object* v_keys_954_, lean_object* v_vals_955_, lean_object* v_heq_956_, lean_object* v_i_957_, lean_object* v_entries_958_){
_start:
{
size_t v_depth_boxed_959_; lean_object* v_res_960_; 
v_depth_boxed_959_ = lean_unbox_usize(v_depth_953_);
lean_dec(v_depth_953_);
v_res_960_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_952_, v_depth_boxed_959_, v_keys_954_, v_vals_955_, v_heq_956_, v_i_957_, v_entries_958_);
lean_dec_ref(v_vals_955_);
lean_dec_ref(v_keys_954_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_961_, lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_969_, lean_object* v_msg_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b1_969_, v_msg_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_977_, lean_object* v_keys_978_, lean_object* v_vals_979_, lean_object* v_heq_980_, lean_object* v_i_981_, lean_object* v_k_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_978_, v_vals_979_, v_i_981_, v_k_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_984_, lean_object* v_keys_985_, lean_object* v_vals_986_, lean_object* v_heq_987_, lean_object* v_i_988_, lean_object* v_k_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(v_00_u03b2_984_, v_keys_985_, v_vals_986_, v_heq_987_, v_i_988_, v_k_989_);
lean_dec_ref(v_k_989_);
lean_dec_ref(v_vals_986_);
lean_dec_ref(v_keys_985_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_991_, lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_x_992_, v_x_993_, v_x_994_, v_x_995_);
return v___x_996_;
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
