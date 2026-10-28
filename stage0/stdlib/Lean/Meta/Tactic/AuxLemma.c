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
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_defeqAttr;
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
static const lean_string_object l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "auxLemmasExt"};
static const lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(95, 124, 117, 209, 228, 238, 156, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_auxLemmasExt;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__0;
static lean_once_cell_t l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1;
static lean_once_cell_t l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2;
static lean_once_cell_t l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkAuxLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_proof"};
static const lean_object* l_Lean_Meta_mkAuxLemma___closed__0 = (const lean_object*)&l_Lean_Meta_mkAuxLemma___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkAuxLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkAuxLemma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 32, 192, 173, 72, 22, 234, 250)}};
static const lean_object* l_Lean_Meta_mkAuxLemma___closed__1 = (const lean_object*)&l_Lean_Meta_mkAuxLemma___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
if (v_isPrivate_4_ == 0)
{
return v_isPrivate_4_;
}
else
{
v___y_10_ = v_isPrivate_4_;
goto v___jp_9_;
}
}
}
v___jp_9_:
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
lean_object* v___f_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; 
v___f_60_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_box(1);
v___x_63_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_));
v___x_64_ = 0;
v___x_65_ = l_Lean_registerEnvExtension___redArg(v___f_60_, v___x_61_, v___x_62_, v___x_63_, v___x_64_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(lean_object* v_kind_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v_auxDeclNGen_72_; lean_object* v___x_73_; lean_object* v_env_74_; lean_object* v___x_75_; lean_object* v_fst_76_; lean_object* v_snd_77_; lean_object* v___x_78_; lean_object* v_env_79_; lean_object* v_nextMacroScope_80_; lean_object* v_ngen_81_; lean_object* v_traceState_82_; lean_object* v_cache_83_; lean_object* v_recordedDeps_84_; lean_object* v_messages_85_; lean_object* v_infoState_86_; lean_object* v_snapshotTasks_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_96_; 
v___x_71_ = lean_st_ref_get(v___y_69_);
v_auxDeclNGen_72_ = lean_ctor_get(v___x_71_, 3);
lean_inc_ref(v_auxDeclNGen_72_);
lean_dec(v___x_71_);
v___x_73_ = lean_st_ref_get(v___y_69_);
v_env_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc_ref(v_env_74_);
lean_dec(v___x_73_);
v___x_75_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_74_, v_auxDeclNGen_72_, v_kind_68_);
v_fst_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_fst_76_);
v_snd_77_ = lean_ctor_get(v___x_75_, 1);
lean_inc(v_snd_77_);
lean_dec_ref(v___x_75_);
v___x_78_ = lean_st_ref_take(v___y_69_);
v_env_79_ = lean_ctor_get(v___x_78_, 0);
v_nextMacroScope_80_ = lean_ctor_get(v___x_78_, 1);
v_ngen_81_ = lean_ctor_get(v___x_78_, 2);
v_traceState_82_ = lean_ctor_get(v___x_78_, 4);
v_cache_83_ = lean_ctor_get(v___x_78_, 5);
v_recordedDeps_84_ = lean_ctor_get(v___x_78_, 6);
v_messages_85_ = lean_ctor_get(v___x_78_, 7);
v_infoState_86_ = lean_ctor_get(v___x_78_, 8);
v_snapshotTasks_87_ = lean_ctor_get(v___x_78_, 9);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v___x_78_, 3);
lean_dec(v_unused_97_);
v___x_89_ = v___x_78_;
v_isShared_90_ = v_isSharedCheck_96_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_snapshotTasks_87_);
lean_inc(v_infoState_86_);
lean_inc(v_messages_85_);
lean_inc(v_recordedDeps_84_);
lean_inc(v_cache_83_);
lean_inc(v_traceState_82_);
lean_inc(v_ngen_81_);
lean_inc(v_nextMacroScope_80_);
lean_inc(v_env_79_);
lean_dec(v___x_78_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_96_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 3, v_snd_77_);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_env_79_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_nextMacroScope_80_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v_ngen_81_);
lean_ctor_set(v_reuseFailAlloc_95_, 3, v_snd_77_);
lean_ctor_set(v_reuseFailAlloc_95_, 4, v_traceState_82_);
lean_ctor_set(v_reuseFailAlloc_95_, 5, v_cache_83_);
lean_ctor_set(v_reuseFailAlloc_95_, 6, v_recordedDeps_84_);
lean_ctor_set(v_reuseFailAlloc_95_, 7, v_messages_85_);
lean_ctor_set(v_reuseFailAlloc_95_, 8, v_infoState_86_);
lean_ctor_set(v_reuseFailAlloc_95_, 9, v_snapshotTasks_87_);
v___x_92_ = v_reuseFailAlloc_95_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_st_ref_put(v___y_69_, v___x_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v_fst_76_);
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg___boxed(lean_object* v_kind_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_98_, v___y_99_);
lean_dec(v___y_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(lean_object* v_kind_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_102_, v___y_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___boxed(lean_object* v_kind_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(v_kind_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__8___redArg(lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
lean_object* v_ks_120_; lean_object* v_vs_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_145_; 
v_ks_120_ = lean_ctor_get(v_x_116_, 0);
v_vs_121_ = lean_ctor_get(v_x_116_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_x_116_);
if (v_isSharedCheck_145_ == 0)
{
v___x_123_ = v_x_116_;
v_isShared_124_ = v_isSharedCheck_145_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_vs_121_);
lean_inc(v_ks_120_);
lean_dec(v_x_116_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_145_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_array_get_size(v_ks_120_);
v___x_126_ = lean_nat_dec_lt(v_x_117_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
lean_dec(v_x_117_);
v___x_127_ = lean_array_push(v_ks_120_, v_x_118_);
v___x_128_ = lean_array_push(v_vs_121_, v_x_119_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_128_);
lean_ctor_set(v___x_123_, 0, v___x_127_);
v___x_130_ = v___x_123_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
else
{
lean_object* v_k_x27_132_; uint8_t v___x_133_; 
v_k_x27_132_ = lean_array_fget_borrowed(v_ks_120_, v_x_117_);
v___x_133_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_118_, v_k_x27_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_135_; 
if (v_isShared_124_ == 0)
{
v___x_135_ = v___x_123_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_ks_120_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_vs_121_);
v___x_135_ = v_reuseFailAlloc_139_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_x_117_, v___x_136_);
lean_dec(v_x_117_);
v_x_116_ = v___x_135_;
v_x_117_ = v___x_137_;
goto _start;
}
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_array_fset(v_ks_120_, v_x_117_, v_x_118_);
v___x_141_ = lean_array_fset(v_vs_121_, v_x_117_, v_x_119_);
lean_dec(v_x_117_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_141_);
lean_ctor_set(v___x_123_, 0, v___x_140_);
v___x_143_ = v___x_123_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(lean_object* v_n_146_, lean_object* v_k_147_, lean_object* v_v_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__8___redArg(v_n_146_, v___x_149_, v_k_147_, v_v_148_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object* v_x_152_, size_t v_x_153_, size_t v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v_es_157_; size_t v___x_158_; size_t v___x_159_; lean_object* v_j_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_es_157_ = lean_ctor_get(v_x_152_, 0);
v___x_158_ = ((size_t)31ULL);
v___x_159_ = lean_usize_land(v_x_153_, v___x_158_);
v_j_160_ = lean_usize_to_nat(v___x_159_);
v___x_161_ = lean_array_get_size(v_es_157_);
v___x_162_ = lean_nat_dec_lt(v_j_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_dec(v_j_160_);
lean_dec(v_x_156_);
lean_dec_ref(v_x_155_);
return v_x_152_;
}
else
{
lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_201_; 
lean_inc_ref(v_es_157_);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; 
v_unused_202_ = lean_ctor_get(v_x_152_, 0);
lean_dec(v_unused_202_);
v___x_164_ = v_x_152_;
v_isShared_165_ = v_isSharedCheck_201_;
goto v_resetjp_163_;
}
else
{
lean_dec(v_x_152_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_201_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_v_166_; lean_object* v___x_167_; lean_object* v_xs_x27_168_; lean_object* v___y_170_; 
v_v_166_ = lean_array_fget(v_es_157_, v_j_160_);
v___x_167_ = lean_box(0);
v_xs_x27_168_ = lean_array_fset(v_es_157_, v_j_160_, v___x_167_);
switch(lean_obj_tag(v_v_166_))
{
case 0:
{
lean_object* v_key_175_; lean_object* v_val_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_186_; 
v_key_175_ = lean_ctor_get(v_v_166_, 0);
v_val_176_ = lean_ctor_get(v_v_166_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v_v_166_);
if (v_isSharedCheck_186_ == 0)
{
v___x_178_ = v_v_166_;
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_val_176_);
lean_inc(v_key_175_);
lean_dec(v_v_166_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
uint8_t v___x_180_; 
v___x_180_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_155_, v_key_175_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_del_object(v___x_178_);
v___x_181_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_175_, v_val_176_, v_x_155_, v_x_156_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
v___y_170_ = v___x_182_;
goto v___jp_169_;
}
else
{
lean_object* v___x_184_; 
lean_dec(v_val_176_);
lean_dec(v_key_175_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_x_156_);
lean_ctor_set(v___x_178_, 0, v_x_155_);
v___x_184_ = v___x_178_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_x_155_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_x_156_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
v___y_170_ = v___x_184_;
goto v___jp_169_;
}
}
}
}
case 1:
{
lean_object* v_node_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_199_; 
v_node_187_ = lean_ctor_get(v_v_166_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v_v_166_);
if (v_isSharedCheck_199_ == 0)
{
v___x_189_ = v_v_166_;
v_isShared_190_ = v_isSharedCheck_199_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_node_187_);
lean_dec(v_v_166_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_199_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_191_ = ((size_t)5ULL);
v___x_192_ = lean_usize_shift_right(v_x_153_, v___x_191_);
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_add(v_x_154_, v___x_193_);
v___x_195_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_node_187_, v___x_192_, v___x_194_, v_x_155_, v_x_156_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_195_);
v___x_197_ = v___x_189_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
v___y_170_ = v___x_197_;
goto v___jp_169_;
}
}
}
default: 
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_x_155_);
lean_ctor_set(v___x_200_, 1, v_x_156_);
v___y_170_ = v___x_200_;
goto v___jp_169_;
}
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_array_fset(v_xs_x27_168_, v_j_160_, v___y_170_);
lean_dec(v_j_160_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_171_);
v___x_173_ = v___x_164_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
else
{
lean_object* v_ks_203_; lean_object* v_vs_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_222_; 
v_ks_203_ = lean_ctor_get(v_x_152_, 0);
v_vs_204_ = lean_ctor_get(v_x_152_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_222_ == 0)
{
v___x_206_ = v_x_152_;
v_isShared_207_ = v_isSharedCheck_222_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_vs_204_);
lean_inc(v_ks_203_);
lean_dec(v_x_152_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_222_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_ks_203_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_vs_204_);
v___x_209_ = v_reuseFailAlloc_221_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v_newNode_210_; size_t v___x_211_; uint8_t v___x_212_; 
v_newNode_210_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v___x_209_, v_x_155_, v_x_156_);
v___x_211_ = ((size_t)7ULL);
v___x_212_ = lean_usize_dec_le(v___x_211_, v_x_154_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_213_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_210_);
v___x_214_ = lean_unsigned_to_nat(4u);
v___x_215_ = lean_nat_dec_lt(v___x_213_, v___x_214_);
lean_dec(v___x_213_);
if (v___x_215_ == 0)
{
lean_object* v_ks_216_; lean_object* v_vs_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_ks_216_ = lean_ctor_get(v_newNode_210_, 0);
lean_inc_ref(v_ks_216_);
v_vs_217_ = lean_ctor_get(v_newNode_210_, 1);
lean_inc_ref(v_vs_217_);
lean_dec_ref(v_newNode_210_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0);
v___x_220_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_x_154_, v_ks_216_, v_vs_217_, v___x_218_, v___x_219_);
lean_dec_ref(v_vs_217_);
lean_dec_ref(v_ks_216_);
return v___x_220_;
}
else
{
return v_newNode_210_;
}
}
else
{
return v_newNode_210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t v_depth_223_, lean_object* v_keys_224_, lean_object* v_vals_225_, lean_object* v_i_226_, lean_object* v_entries_227_){
_start:
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_array_get_size(v_keys_224_);
v___x_229_ = lean_nat_dec_lt(v_i_226_, v___x_228_);
if (v___x_229_ == 0)
{
lean_dec(v_i_226_);
return v_entries_227_;
}
else
{
lean_object* v_k_230_; lean_object* v_v_231_; uint64_t v___x_232_; size_t v_h_233_; size_t v___x_234_; lean_object* v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v_h_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_k_230_ = lean_array_fget_borrowed(v_keys_224_, v_i_226_);
v_v_231_ = lean_array_fget_borrowed(v_vals_225_, v_i_226_);
v___x_232_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_k_230_);
v_h_233_ = lean_uint64_to_usize(v___x_232_);
v___x_234_ = ((size_t)5ULL);
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_sub(v_depth_223_, v___x_236_);
v___x_238_ = lean_usize_mul(v___x_234_, v___x_237_);
v_h_239_ = lean_usize_shift_right(v_h_233_, v___x_238_);
v___x_240_ = lean_nat_add(v_i_226_, v___x_235_);
lean_dec(v_i_226_);
lean_inc(v_v_231_);
lean_inc(v_k_230_);
v___x_241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_entries_227_, v_h_239_, v_depth_223_, v_k_230_, v_v_231_);
v_i_226_ = v___x_240_;
v_entries_227_ = v___x_241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_243_, lean_object* v_keys_244_, lean_object* v_vals_245_, lean_object* v_i_246_, lean_object* v_entries_247_){
_start:
{
size_t v_depth_boxed_248_; lean_object* v_res_249_; 
v_depth_boxed_248_ = lean_unbox_usize(v_depth_243_);
lean_dec(v_depth_243_);
v_res_249_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_boxed_248_, v_keys_244_, v_vals_245_, v_i_246_, v_entries_247_);
lean_dec_ref(v_vals_245_);
lean_dec_ref(v_keys_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
size_t v_x_5782__boxed_255_; size_t v_x_5783__boxed_256_; lean_object* v_res_257_; 
v_x_5782__boxed_255_ = lean_unbox_usize(v_x_251_);
lean_dec(v_x_251_);
v_x_5783__boxed_256_ = lean_unbox_usize(v_x_252_);
lean_dec(v_x_252_);
v_res_257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_250_, v_x_5782__boxed_255_, v_x_5783__boxed_256_, v_x_253_, v_x_254_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
uint64_t v___x_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; 
v___x_261_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_259_);
v___x_262_ = lean_uint64_to_usize(v___x_261_);
v___x_263_ = ((size_t)1ULL);
v___x_264_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_258_, v___x_262_, v___x_263_, v_x_259_, v_x_260_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object* v_a_265_, lean_object* v_levelParams_266_, lean_object* v___x_267_, lean_object* v_x_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v_a_265_);
lean_ctor_set(v___x_269_, 1, v_levelParams_266_);
v___x_270_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_268_, v___x_267_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12___redArg(lean_object* v_keys_271_, lean_object* v_vals_272_, lean_object* v_i_273_, lean_object* v_k_274_){
_start:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_array_get_size(v_keys_271_);
v___x_276_ = lean_nat_dec_lt(v_i_273_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec(v_i_273_);
v___x_277_ = lean_box(0);
return v___x_277_;
}
else
{
lean_object* v_k_x27_278_; uint8_t v___x_279_; 
v_k_x27_278_ = lean_array_fget_borrowed(v_keys_271_, v_i_273_);
v___x_279_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_k_274_, v_k_x27_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v_i_273_, v___x_280_);
lean_dec(v_i_273_);
v_i_273_ = v___x_281_;
goto _start;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_array_fget_borrowed(v_vals_272_, v_i_273_);
lean_dec(v_i_273_);
lean_inc(v___x_283_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_keys_285_, lean_object* v_vals_286_, lean_object* v_i_287_, lean_object* v_k_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12___redArg(v_keys_285_, v_vals_286_, v_i_287_, v_k_288_);
lean_dec_ref(v_k_288_);
lean_dec_ref(v_vals_286_);
lean_dec_ref(v_keys_285_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8___redArg(lean_object* v_x_290_, size_t v_x_291_, lean_object* v_x_292_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v_es_293_; lean_object* v___x_294_; size_t v___x_295_; size_t v___x_296_; lean_object* v_j_297_; lean_object* v___x_298_; 
v_es_293_ = lean_ctor_get(v_x_290_, 0);
v___x_294_ = lean_box(2);
v___x_295_ = ((size_t)31ULL);
v___x_296_ = lean_usize_land(v_x_291_, v___x_295_);
v_j_297_ = lean_usize_to_nat(v___x_296_);
v___x_298_ = lean_array_get_borrowed(v___x_294_, v_es_293_, v_j_297_);
lean_dec(v_j_297_);
switch(lean_obj_tag(v___x_298_))
{
case 0:
{
lean_object* v_key_299_; lean_object* v_val_300_; uint8_t v___x_301_; 
v_key_299_ = lean_ctor_get(v___x_298_, 0);
v_val_300_ = lean_ctor_get(v___x_298_, 1);
v___x_301_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_292_, v_key_299_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_box(0);
return v___x_302_;
}
else
{
lean_object* v___x_303_; 
lean_inc(v_val_300_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v_val_300_);
return v___x_303_;
}
}
case 1:
{
lean_object* v_node_304_; size_t v___x_305_; size_t v___x_306_; 
v_node_304_ = lean_ctor_get(v___x_298_, 0);
v___x_305_ = ((size_t)5ULL);
v___x_306_ = lean_usize_shift_right(v_x_291_, v___x_305_);
v_x_290_ = v_node_304_;
v_x_291_ = v___x_306_;
goto _start;
}
default: 
{
lean_object* v___x_308_; 
v___x_308_ = lean_box(0);
return v___x_308_;
}
}
}
else
{
lean_object* v_ks_309_; lean_object* v_vs_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_ks_309_ = lean_ctor_get(v_x_290_, 0);
v_vs_310_ = lean_ctor_get(v_x_290_, 1);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12___redArg(v_ks_309_, v_vs_310_, v___x_311_, v_x_292_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8___redArg___boxed(lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
size_t v_x_5976__boxed_316_; lean_object* v_res_317_; 
v_x_5976__boxed_316_ = lean_unbox_usize(v_x_314_);
lean_dec(v_x_314_);
v_res_317_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8___redArg(v_x_313_, v_x_5976__boxed_316_, v_x_315_);
lean_dec_ref(v_x_315_);
lean_dec_ref(v_x_313_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4___redArg(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
uint64_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_320_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_319_);
v___x_321_ = lean_uint64_to_usize(v___x_320_);
v___x_322_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8___redArg(v_x_318_, v___x_321_, v_x_319_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4___redArg___boxed(lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4___redArg(v_x_323_, v_x_324_);
lean_dec_ref(v_x_324_);
lean_dec_ref(v_x_323_);
return v_res_325_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__5(lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
if (lean_obj_tag(v_x_327_) == 0)
{
uint8_t v___x_328_; 
v___x_328_ = 1;
return v___x_328_;
}
else
{
uint8_t v___x_329_; 
v___x_329_ = 0;
return v___x_329_;
}
}
else
{
if (lean_obj_tag(v_x_327_) == 0)
{
uint8_t v___x_330_; 
v___x_330_ = 0;
return v___x_330_;
}
else
{
lean_object* v_head_331_; lean_object* v_tail_332_; lean_object* v_head_333_; lean_object* v_tail_334_; uint8_t v___x_335_; 
v_head_331_ = lean_ctor_get(v_x_326_, 0);
v_tail_332_ = lean_ctor_get(v_x_326_, 1);
v_head_333_ = lean_ctor_get(v_x_327_, 0);
v_tail_334_ = lean_ctor_get(v_x_327_, 1);
v___x_335_ = lean_name_eq(v_head_331_, v_head_333_);
if (v___x_335_ == 0)
{
return v___x_335_;
}
else
{
v_x_326_ = v_tail_332_;
v_x_327_ = v_tail_334_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__5___boxed(lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__5(v_x_337_, v_x_338_);
lean_dec(v_x_338_);
lean_dec(v_x_337_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8_spec__12(lean_object* v_msgData_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; lean_object* v_env_348_; uint8_t v___x_349_; lean_object* v_env_350_; lean_object* v___x_351_; lean_object* v_toCold_352_; lean_object* v_mctx_353_; lean_object* v_lctx_354_; lean_object* v_options_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_347_ = lean_st_ref_get(v___y_345_);
v_env_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc_ref(v_env_348_);
lean_dec(v___x_347_);
v___x_349_ = 0;
v_env_350_ = l_Lean_Environment_setRecordingDeps(v_env_348_, v___x_349_);
v___x_351_ = lean_st_ref_get(v___y_343_);
v_toCold_352_ = lean_ctor_get(v___y_344_, 0);
v_mctx_353_ = lean_ctor_get(v___x_351_, 0);
lean_inc_ref(v_mctx_353_);
lean_dec(v___x_351_);
v_lctx_354_ = lean_ctor_get(v___y_342_, 2);
v_options_355_ = lean_ctor_get(v_toCold_352_, 2);
lean_inc_ref(v_options_355_);
lean_inc_ref(v_lctx_354_);
v___x_356_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_356_, 0, v_env_350_);
lean_ctor_set(v___x_356_, 1, v_mctx_353_);
lean_ctor_set(v___x_356_, 2, v_lctx_354_);
lean_ctor_set(v___x_356_, 3, v_options_355_);
v___x_357_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_msgData_341_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8_spec__12___boxed(lean_object* v_msgData_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8_spec__12(v_msgData_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8___redArg(lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_ref_372_; lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
v_ref_372_ = lean_ctor_get(v___y_369_, 2);
v___x_373_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8_spec__12(v_msg_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_382_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
lean_inc(v_ref_372_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_ref_372_);
lean_ctor_set(v___x_378_, 1, v_a_374_);
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 1);
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8___redArg(v_msg_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__0));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__2));
v___x_395_ = l_Lean_stringToMessageData(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__4));
v___x_398_ = l_Lean_stringToMessageData(v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__6));
v___x_401_ = l_Lean_stringToMessageData(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__8));
v___x_404_ = l_Lean_stringToMessageData(v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg(lean_object* v_attrName_405_, lean_object* v_declName_406_, lean_object* v_asyncPrefix_x3f_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___y_414_; 
if (lean_obj_tag(v_asyncPrefix_x3f_407_) == 0)
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_MessageData_nil;
v___y_414_ = v___x_427_;
goto v___jp_413_;
}
else
{
lean_object* v_val_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_val_428_ = lean_ctor_get(v_asyncPrefix_x3f_407_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v_asyncPrefix_x3f_407_, 1);
v___x_429_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__7);
v___x_430_ = l_Lean_MessageData_ofName(v_val_428_);
v___x_431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__9, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__9_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__9);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___y_414_ = v___x_433_;
goto v___jp_413_;
}
v___jp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_415_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__1);
v___x_416_ = l_Lean_MessageData_ofName(v_attrName_405_);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__3);
v___x_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = 0;
v___x_421_ = l_Lean_MessageData_ofConstName(v_declName_406_, v___x_420_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_419_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__5);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___y_414_);
v___x_426_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8___redArg(v___x_425_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___boxed(lean_object* v_attrName_434_, lean_object* v_declName_435_, lean_object* v_asyncPrefix_x3f_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg(v_attrName_434_, v_declName_435_, v_asyncPrefix_x3f_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___lam__0(lean_object* v_addEntryFn_443_, lean_object* v_decl_444_, lean_object* v_s_445_){
_start:
{
lean_object* v_importedEntries_446_; lean_object* v_state_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
v_importedEntries_446_ = lean_ctor_get(v_s_445_, 0);
v_state_447_ = lean_ctor_get(v_s_445_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_s_445_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v_s_445_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_state_447_);
lean_inc(v_importedEntries_446_);
lean_dec(v_s_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_state_451_; lean_object* v___x_453_; 
v_state_451_ = lean_apply_2(v_addEntryFn_443_, v_state_447_, v_decl_444_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_state_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_importedEntries_446_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_state_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object* v___dummy_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg();
return v_res_461_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___closed__0));
v___x_464_ = l_Lean_stringToMessageData(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(lean_object* v_attrName_465_, lean_object* v_declName_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_472_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__1);
v___x_473_ = l_Lean_MessageData_ofName(v_attrName_465_);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg___closed__3);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = 0;
v___x_478_ = l_Lean_MessageData_ofConstName(v_declName_466_, v___x_477_);
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_476_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___closed__1);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8___redArg(v___x_481_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(lean_object* v_attrName_483_, lean_object* v_declName_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_attrName_483_, v_declName_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_490_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__0(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__0);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2(void){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg();
return v___x_495_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__0);
v___x_497_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2);
v___x_498_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___x_496_);
lean_ctor_set(v___x_498_, 2, v___x_496_);
lean_ctor_set(v___x_498_, 3, v___x_496_);
lean_ctor_set(v___x_498_, 4, v___x_496_);
lean_ctor_set(v___x_498_, 5, v___x_496_);
lean_ctor_set(v___x_498_, 6, v___x_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_attr_499_, lean_object* v_decl_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___x_561_; lean_object* v_env_562_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___x_577_; 
v___x_561_ = lean_st_ref_get(v___y_504_);
v_env_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_env_562_);
lean_dec(v___x_561_);
v___x_577_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_562_, v_decl_500_);
if (lean_obj_tag(v___x_577_) == 0)
{
v___y_564_ = v___y_501_;
v___y_565_ = v___y_502_;
v___y_566_ = v___y_503_;
v___y_567_ = v___y_504_;
goto v___jp_563_;
}
else
{
lean_object* v_attr_578_; lean_object* v_toAttributeImplCore_579_; lean_object* v_name_580_; lean_object* v___x_581_; 
lean_dec_ref_known(v___x_577_, 1);
lean_dec_ref(v_env_562_);
v_attr_578_ = lean_ctor_get(v_attr_499_, 0);
lean_inc_ref(v_attr_578_);
lean_dec_ref(v_attr_499_);
v_toAttributeImplCore_579_ = lean_ctor_get(v_attr_578_, 0);
lean_inc_ref(v_toAttributeImplCore_579_);
lean_dec_ref(v_attr_578_);
v_name_580_ = lean_ctor_get(v_toAttributeImplCore_579_, 1);
lean_inc(v_name_580_);
lean_dec_ref(v_toAttributeImplCore_579_);
v___x_581_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_name_580_, v_decl_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_581_;
}
v___jp_506_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_mctx_522_; lean_object* v_zetaDeltaFVarIds_523_; lean_object* v_postponed_524_; lean_object* v_diag_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_536_; 
v___x_518_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1);
v___x_519_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_519_, 0, v___y_517_);
lean_ctor_set(v___x_519_, 1, v___y_515_);
lean_ctor_set(v___x_519_, 2, v___y_516_);
lean_ctor_set(v___x_519_, 3, v___y_513_);
lean_ctor_set(v___x_519_, 4, v___y_514_);
lean_ctor_set(v___x_519_, 5, v___x_518_);
lean_ctor_set(v___x_519_, 6, v___y_512_);
lean_ctor_set(v___x_519_, 7, v___y_507_);
lean_ctor_set(v___x_519_, 8, v___y_509_);
lean_ctor_set(v___x_519_, 9, v___y_511_);
v___x_520_ = lean_st_ref_put(v___y_508_, v___x_519_);
v___x_521_ = lean_st_ref_take(v___y_510_);
v_mctx_522_ = lean_ctor_get(v___x_521_, 0);
v_zetaDeltaFVarIds_523_ = lean_ctor_get(v___x_521_, 2);
v_postponed_524_ = lean_ctor_get(v___x_521_, 3);
v_diag_525_ = lean_ctor_get(v___x_521_, 4);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v___x_521_, 1);
lean_dec(v_unused_537_);
v___x_527_ = v___x_521_;
v_isShared_528_ = v_isSharedCheck_536_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_diag_525_);
lean_inc(v_postponed_524_);
lean_inc(v_zetaDeltaFVarIds_523_);
lean_inc(v_mctx_522_);
lean_dec(v___x_521_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_536_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_529_ = lean_box(0);
v___x_530_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v___x_530_);
v___x_532_ = v___x_527_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_mctx_522_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_zetaDeltaFVarIds_523_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_postponed_524_);
lean_ctor_set(v_reuseFailAlloc_535_, 4, v_diag_525_);
v___x_532_ = v_reuseFailAlloc_535_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_st_ref_put(v___y_510_, v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_529_);
return v___x_534_;
}
}
}
v___jp_538_:
{
lean_object* v___x_541_; lean_object* v_ext_542_; lean_object* v_toEnvExtension_543_; lean_object* v_env_544_; lean_object* v_nextMacroScope_545_; lean_object* v_ngen_546_; lean_object* v_auxDeclNGen_547_; lean_object* v_traceState_548_; lean_object* v_recordedDeps_549_; lean_object* v_messages_550_; lean_object* v_infoState_551_; lean_object* v_snapshotTasks_552_; lean_object* v_addEntryFn_553_; lean_object* v_asyncMode_554_; uint8_t v_logWrites_555_; lean_object* v___f_556_; uint8_t v___x_557_; 
v___x_541_ = lean_st_ref_take(v___y_540_);
v_ext_542_ = lean_ctor_get(v_attr_499_, 1);
lean_inc_ref(v_ext_542_);
lean_dec_ref(v_attr_499_);
v_toEnvExtension_543_ = lean_ctor_get(v_ext_542_, 0);
lean_inc_ref(v_toEnvExtension_543_);
v_env_544_ = lean_ctor_get(v___x_541_, 0);
lean_inc_ref(v_env_544_);
v_nextMacroScope_545_ = lean_ctor_get(v___x_541_, 1);
lean_inc(v_nextMacroScope_545_);
v_ngen_546_ = lean_ctor_get(v___x_541_, 2);
lean_inc_ref(v_ngen_546_);
v_auxDeclNGen_547_ = lean_ctor_get(v___x_541_, 3);
lean_inc_ref(v_auxDeclNGen_547_);
v_traceState_548_ = lean_ctor_get(v___x_541_, 4);
lean_inc_ref(v_traceState_548_);
v_recordedDeps_549_ = lean_ctor_get(v___x_541_, 6);
lean_inc_ref(v_recordedDeps_549_);
v_messages_550_ = lean_ctor_get(v___x_541_, 7);
lean_inc_ref(v_messages_550_);
v_infoState_551_ = lean_ctor_get(v___x_541_, 8);
lean_inc_ref(v_infoState_551_);
v_snapshotTasks_552_ = lean_ctor_get(v___x_541_, 9);
lean_inc_ref(v_snapshotTasks_552_);
lean_dec(v___x_541_);
v_addEntryFn_553_ = lean_ctor_get(v_ext_542_, 3);
lean_inc(v_addEntryFn_553_);
lean_dec_ref(v_ext_542_);
v_asyncMode_554_ = lean_ctor_get(v_toEnvExtension_543_, 2);
lean_inc(v_asyncMode_554_);
v_logWrites_555_ = lean_ctor_get_uint8(v_toEnvExtension_543_, sizeof(void*)*6);
lean_inc(v_decl_500_);
v___f_556_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_556_, 0, v_addEntryFn_553_);
lean_closure_set(v___f_556_, 1, v_decl_500_);
v___x_557_ = 1;
if (v_logWrites_555_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_543_, v_env_544_, v___f_556_, v_asyncMode_554_, v_decl_500_, v___x_557_);
lean_dec(v_asyncMode_554_);
v___y_507_ = v_messages_550_;
v___y_508_ = v___y_540_;
v___y_509_ = v_infoState_551_;
v___y_510_ = v___y_539_;
v___y_511_ = v_snapshotTasks_552_;
v___y_512_ = v_recordedDeps_549_;
v___y_513_ = v_auxDeclNGen_547_;
v___y_514_ = v_traceState_548_;
v___y_515_ = v_nextMacroScope_545_;
v___y_516_ = v_ngen_546_;
v___y_517_ = v___x_558_;
goto v___jp_506_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_inc_ref(v_toEnvExtension_543_);
v___x_559_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_543_, v_env_544_);
lean_dec_ref(v_env_544_);
v___x_560_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_543_, v___x_559_, v___f_556_, v_asyncMode_554_, v_decl_500_, v___x_557_);
lean_dec(v_asyncMode_554_);
v___y_507_ = v_messages_550_;
v___y_508_ = v___y_540_;
v___y_509_ = v_infoState_551_;
v___y_510_ = v___y_539_;
v___y_511_ = v_snapshotTasks_552_;
v___y_512_ = v_recordedDeps_549_;
v___y_513_ = v_auxDeclNGen_547_;
v___y_514_ = v_traceState_548_;
v___y_515_ = v_nextMacroScope_545_;
v___y_516_ = v_ngen_546_;
v___y_517_ = v___x_560_;
goto v___jp_506_;
}
}
v___jp_563_:
{
lean_object* v_ext_568_; lean_object* v_toEnvExtension_569_; lean_object* v_attr_570_; lean_object* v_asyncMode_571_; uint8_t v___x_572_; 
v_ext_568_ = lean_ctor_get(v_attr_499_, 1);
v_toEnvExtension_569_ = lean_ctor_get(v_ext_568_, 0);
v_attr_570_ = lean_ctor_get(v_attr_499_, 0);
v_asyncMode_571_ = lean_ctor_get(v_toEnvExtension_569_, 2);
lean_inc(v_decl_500_);
lean_inc_ref(v_env_562_);
v___x_572_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_562_, v_decl_500_, v_asyncMode_571_);
if (v___x_572_ == 0)
{
lean_object* v_toAttributeImplCore_573_; lean_object* v_name_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_inc_ref(v_attr_570_);
lean_dec_ref(v_attr_499_);
v_toAttributeImplCore_573_ = lean_ctor_get(v_attr_570_, 0);
lean_inc_ref(v_toAttributeImplCore_573_);
lean_dec_ref(v_attr_570_);
v_name_574_ = lean_ctor_get(v_toAttributeImplCore_573_, 1);
lean_inc(v_name_574_);
lean_dec_ref(v_toAttributeImplCore_573_);
v___x_575_ = l_Lean_Environment_asyncPrefix_x3f(v_env_562_);
v___x_576_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg(v_name_574_, v_decl_500_, v___x_575_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
return v___x_576_;
}
else
{
lean_dec_ref(v_env_562_);
v___y_539_ = v___y_565_;
v___y_540_ = v___y_567_;
goto v___jp_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_attr_582_, lean_object* v_decl_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3(v_attr_582_, v_decl_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object* v_levelParams_593_, lean_object* v_type_594_, lean_object* v_value_595_, lean_object* v_kind_x3f_596_, uint8_t v_cache_597_, uint8_t v_inferRfl_598_, uint8_t v_forceExpose_599_, uint8_t v_defeq_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v_nextMacroScope_609_; lean_object* v_ngen_610_; lean_object* v_auxDeclNGen_611_; lean_object* v_traceState_612_; lean_object* v_recordedDeps_613_; lean_object* v_messages_614_; lean_object* v_infoState_615_; lean_object* v_snapshotTasks_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_639_; lean_object* v_nextMacroScope_640_; lean_object* v_ngen_641_; lean_object* v_auxDeclNGen_642_; lean_object* v_traceState_643_; lean_object* v_recordedDeps_644_; lean_object* v_messages_645_; lean_object* v_infoState_646_; lean_object* v_snapshotTasks_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_env_672_; lean_object* v___x_673_; lean_object* v_asyncMode_674_; uint8_t v_logWrites_675_; uint8_t v_isExporting_676_; lean_object* v___x_677_; lean_object* v___y_679_; uint8_t v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_707_; uint8_t v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; uint8_t v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_791_; lean_object* v___y_792_; uint8_t v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_819_; lean_object* v___y_820_; uint8_t v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_836_; lean_object* v___y_837_; uint8_t v___y_838_; lean_object* v___y_839_; lean_object* v___y_860_; lean_object* v___y_861_; uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___y_873_; uint8_t v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; uint8_t v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; uint8_t v___y_927_; 
v___x_670_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_671_ = lean_st_ref_get(v_a_604_);
v_env_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref_n(v_env_672_, 2);
lean_dec(v___x_671_);
v___x_673_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_674_ = lean_ctor_get(v___x_673_, 2);
v_logWrites_675_ = lean_ctor_get_uint8(v___x_673_, sizeof(void*)*6);
v_isExporting_676_ = lean_ctor_get_uint8(v_env_672_, sizeof(void*)*13);
v___x_677_ = lean_box(0);
v___x_870_ = 0;
v___x_871_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_670_, v___x_673_, v_env_672_, v_asyncMode_674_, v___x_677_, v___x_870_);
if (v_isExporting_676_ == 0)
{
uint8_t v___x_931_; 
v___x_931_ = 1;
v___y_927_ = v___x_931_;
goto v___jp_926_;
}
else
{
v___y_927_ = v___x_870_;
goto v___jp_926_;
}
v___jp_606_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_mctx_623_; lean_object* v_zetaDeltaFVarIds_624_; lean_object* v_postponed_625_; lean_object* v_diag_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_636_; 
v___x_619_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1);
v___x_620_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_620_, 0, v___y_618_);
lean_ctor_set(v___x_620_, 1, v_nextMacroScope_609_);
lean_ctor_set(v___x_620_, 2, v_ngen_610_);
lean_ctor_set(v___x_620_, 3, v_auxDeclNGen_611_);
lean_ctor_set(v___x_620_, 4, v_traceState_612_);
lean_ctor_set(v___x_620_, 5, v___x_619_);
lean_ctor_set(v___x_620_, 6, v_recordedDeps_613_);
lean_ctor_set(v___x_620_, 7, v_messages_614_);
lean_ctor_set(v___x_620_, 8, v_infoState_615_);
lean_ctor_set(v___x_620_, 9, v_snapshotTasks_616_);
v___x_621_ = lean_st_ref_put(v___y_617_, v___x_620_);
v___x_622_ = lean_st_ref_take(v___y_607_);
v_mctx_623_ = lean_ctor_get(v___x_622_, 0);
v_zetaDeltaFVarIds_624_ = lean_ctor_get(v___x_622_, 2);
v_postponed_625_ = lean_ctor_get(v___x_622_, 3);
v_diag_626_ = lean_ctor_get(v___x_622_, 4);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; 
v_unused_637_ = lean_ctor_get(v___x_622_, 1);
lean_dec(v_unused_637_);
v___x_628_ = v___x_622_;
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_diag_626_);
lean_inc(v_postponed_625_);
lean_inc(v_zetaDeltaFVarIds_624_);
lean_inc(v_mctx_623_);
lean_dec(v___x_622_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_mctx_623_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_zetaDeltaFVarIds_624_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_postponed_625_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_diag_626_);
v___x_632_ = v_reuseFailAlloc_635_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_st_ref_put(v___y_607_, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___y_608_);
return v___x_634_;
}
}
}
v___jp_638_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_mctx_655_; lean_object* v_zetaDeltaFVarIds_656_; lean_object* v_postponed_657_; lean_object* v_diag_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_668_; 
v___x_651_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__1);
v___x_652_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_652_, 0, v___y_650_);
lean_ctor_set(v___x_652_, 1, v_nextMacroScope_640_);
lean_ctor_set(v___x_652_, 2, v_ngen_641_);
lean_ctor_set(v___x_652_, 3, v_auxDeclNGen_642_);
lean_ctor_set(v___x_652_, 4, v_traceState_643_);
lean_ctor_set(v___x_652_, 5, v___x_651_);
lean_ctor_set(v___x_652_, 6, v_recordedDeps_644_);
lean_ctor_set(v___x_652_, 7, v_messages_645_);
lean_ctor_set(v___x_652_, 8, v_infoState_646_);
lean_ctor_set(v___x_652_, 9, v_snapshotTasks_647_);
v___x_653_ = lean_st_ref_put(v___y_649_, v___x_652_);
v___x_654_ = lean_st_ref_take(v___y_639_);
v_mctx_655_ = lean_ctor_get(v___x_654_, 0);
v_zetaDeltaFVarIds_656_ = lean_ctor_get(v___x_654_, 2);
v_postponed_657_ = lean_ctor_get(v___x_654_, 3);
v_diag_658_ = lean_ctor_get(v___x_654_, 4);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v___x_654_, 1);
lean_dec(v_unused_669_);
v___x_660_ = v___x_654_;
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_diag_658_);
lean_inc(v_postponed_657_);
lean_inc(v_zetaDeltaFVarIds_656_);
lean_inc(v_mctx_655_);
lean_dec(v___x_654_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__3);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_mctx_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_zetaDeltaFVarIds_656_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_postponed_657_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v_diag_658_);
v___x_664_ = v_reuseFailAlloc_667_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_st_ref_put(v___y_639_, v___x_664_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___y_648_);
return v___x_666_;
}
}
}
v___jp_678_:
{
lean_object* v___x_684_; 
v___x_684_ = lean_st_ref_take(v___y_683_);
if (v_logWrites_675_ == 0)
{
lean_object* v_env_685_; lean_object* v_nextMacroScope_686_; lean_object* v_ngen_687_; lean_object* v_auxDeclNGen_688_; lean_object* v_traceState_689_; lean_object* v_recordedDeps_690_; lean_object* v_messages_691_; lean_object* v_infoState_692_; lean_object* v_snapshotTasks_693_; lean_object* v___x_694_; 
v_env_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_ref(v_env_685_);
v_nextMacroScope_686_ = lean_ctor_get(v___x_684_, 1);
lean_inc(v_nextMacroScope_686_);
v_ngen_687_ = lean_ctor_get(v___x_684_, 2);
lean_inc_ref(v_ngen_687_);
v_auxDeclNGen_688_ = lean_ctor_get(v___x_684_, 3);
lean_inc_ref(v_auxDeclNGen_688_);
v_traceState_689_ = lean_ctor_get(v___x_684_, 4);
lean_inc_ref(v_traceState_689_);
v_recordedDeps_690_ = lean_ctor_get(v___x_684_, 6);
lean_inc_ref(v_recordedDeps_690_);
v_messages_691_ = lean_ctor_get(v___x_684_, 7);
lean_inc_ref(v_messages_691_);
v_infoState_692_ = lean_ctor_get(v___x_684_, 8);
lean_inc_ref(v_infoState_692_);
v_snapshotTasks_693_ = lean_ctor_get(v___x_684_, 9);
lean_inc_ref(v_snapshotTasks_693_);
lean_dec(v___x_684_);
v___x_694_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_673_, v_env_685_, v___y_681_, v_asyncMode_674_, v___x_677_, v___y_680_);
v___y_607_ = v___y_682_;
v___y_608_ = v___y_679_;
v_nextMacroScope_609_ = v_nextMacroScope_686_;
v_ngen_610_ = v_ngen_687_;
v_auxDeclNGen_611_ = v_auxDeclNGen_688_;
v_traceState_612_ = v_traceState_689_;
v_recordedDeps_613_ = v_recordedDeps_690_;
v_messages_614_ = v_messages_691_;
v_infoState_615_ = v_infoState_692_;
v_snapshotTasks_616_ = v_snapshotTasks_693_;
v___y_617_ = v___y_683_;
v___y_618_ = v___x_694_;
goto v___jp_606_;
}
else
{
lean_object* v_env_695_; lean_object* v_nextMacroScope_696_; lean_object* v_ngen_697_; lean_object* v_auxDeclNGen_698_; lean_object* v_traceState_699_; lean_object* v_recordedDeps_700_; lean_object* v_messages_701_; lean_object* v_infoState_702_; lean_object* v_snapshotTasks_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_env_695_ = lean_ctor_get(v___x_684_, 0);
lean_inc_ref(v_env_695_);
v_nextMacroScope_696_ = lean_ctor_get(v___x_684_, 1);
lean_inc(v_nextMacroScope_696_);
v_ngen_697_ = lean_ctor_get(v___x_684_, 2);
lean_inc_ref(v_ngen_697_);
v_auxDeclNGen_698_ = lean_ctor_get(v___x_684_, 3);
lean_inc_ref(v_auxDeclNGen_698_);
v_traceState_699_ = lean_ctor_get(v___x_684_, 4);
lean_inc_ref(v_traceState_699_);
v_recordedDeps_700_ = lean_ctor_get(v___x_684_, 6);
lean_inc_ref(v_recordedDeps_700_);
v_messages_701_ = lean_ctor_get(v___x_684_, 7);
lean_inc_ref(v_messages_701_);
v_infoState_702_ = lean_ctor_get(v___x_684_, 8);
lean_inc_ref(v_infoState_702_);
v_snapshotTasks_703_ = lean_ctor_get(v___x_684_, 9);
lean_inc_ref(v_snapshotTasks_703_);
lean_dec(v___x_684_);
v___x_704_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_673_, v_env_695_);
lean_dec_ref(v_env_695_);
v___x_705_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_673_, v___x_704_, v___y_681_, v_asyncMode_674_, v___x_677_, v___y_680_);
v___y_607_ = v___y_682_;
v___y_608_ = v___y_679_;
v_nextMacroScope_609_ = v_nextMacroScope_696_;
v_ngen_610_ = v_ngen_697_;
v_auxDeclNGen_611_ = v_auxDeclNGen_698_;
v_traceState_612_ = v_traceState_699_;
v_recordedDeps_613_ = v_recordedDeps_700_;
v_messages_614_ = v_messages_701_;
v_infoState_615_ = v_infoState_702_;
v_snapshotTasks_616_ = v_snapshotTasks_703_;
v___y_617_ = v___y_683_;
v___y_618_ = v___x_705_;
goto v___jp_606_;
}
}
v___jp_706_:
{
if (v_inferRfl_598_ == 0)
{
v___y_679_ = v___y_707_;
v___y_680_ = v___y_708_;
v___y_681_ = v___y_709_;
v___y_682_ = v___y_711_;
v___y_683_ = v___y_713_;
goto v___jp_678_;
}
else
{
lean_object* v___x_714_; 
lean_inc(v___y_707_);
v___x_714_ = l_Lean_inferDefEqAttr(v___y_707_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_dec_ref_known(v___x_714_, 1);
v___y_679_ = v___y_707_;
v___y_680_ = v___y_708_;
v___y_681_ = v___y_709_;
v___y_682_ = v___y_711_;
v___y_683_ = v___y_713_;
goto v___jp_678_;
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec_ref(v___y_709_);
lean_dec(v___y_707_);
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
lean_object* v___x_732_; 
v___x_732_ = l_Lean_addDecl(v___y_731_, v_forceExpose_599_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_dec_ref_known(v___x_732_, 1);
if (v_defeq_600_ == 0)
{
v___y_707_ = v___y_725_;
v___y_708_ = v___y_727_;
v___y_709_ = v___y_730_;
v___y_710_ = v___y_726_;
v___y_711_ = v___y_724_;
v___y_712_ = v___y_728_;
v___y_713_ = v___y_729_;
goto v___jp_706_;
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = l_Lean_defeqAttr;
lean_inc(v___y_725_);
v___x_734_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3(v___x_733_, v___y_725_, v___y_726_, v___y_724_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_dec_ref_known(v___x_734_, 1);
v___y_707_ = v___y_725_;
v___y_708_ = v___y_727_;
v___y_709_ = v___y_730_;
v___y_710_ = v___y_726_;
v___y_711_ = v___y_724_;
v___y_712_ = v___y_728_;
v___y_713_ = v___y_729_;
goto v___jp_706_;
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v___y_730_);
lean_dec(v___y_725_);
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v___y_730_);
lean_dec(v___y_725_);
v_a_743_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_732_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_732_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
v___jp_751_:
{
uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_758_ = 1;
lean_inc_n(v___y_753_, 2);
v___x_759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_759_, 0, v___y_753_);
lean_ctor_set(v___x_759_, 1, v_levelParams_593_);
lean_ctor_set(v___x_759_, 2, v_type_594_);
v___x_760_ = lean_box(0);
v___x_761_ = 0;
v___x_762_ = lean_box(0);
v___x_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_763_, 0, v___y_753_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_764_, 0, v___x_759_);
lean_ctor_set(v___x_764_, 1, v_value_595_);
lean_ctor_set(v___x_764_, 2, v___x_760_);
lean_ctor_set(v___x_764_, 3, v___x_763_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*4, v___x_761_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
v___y_724_ = v___y_752_;
v___y_725_ = v___y_753_;
v___y_726_ = v___y_754_;
v___y_727_ = v___x_758_;
v___y_728_ = v___y_755_;
v___y_729_ = v___y_756_;
v___y_730_ = v___y_757_;
v___y_731_ = v___x_765_;
goto v___jp_723_;
}
v___jp_766_:
{
lean_object* v___x_773_; lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_789_; 
v___x_773_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_768_, v___y_772_);
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_789_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_789_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_789_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___f_778_; uint8_t v___x_779_; 
lean_inc(v_levelParams_593_);
lean_inc(v_a_774_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_778_, 0, v_a_774_);
lean_closure_set(v___f_778_, 1, v_levelParams_593_);
lean_closure_set(v___f_778_, 2, v___y_767_);
lean_inc_ref(v_env_672_);
v___x_779_ = l_Lean_Environment_hasUnsafe(v_env_672_, v_type_594_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; 
v___x_780_ = l_Lean_Environment_hasUnsafe(v_env_672_, v_value_595_);
if (v___x_780_ == 0)
{
uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_781_ = 1;
lean_inc_n(v_a_774_, 2);
v___x_782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_782_, 0, v_a_774_);
lean_ctor_set(v___x_782_, 1, v_levelParams_593_);
lean_ctor_set(v___x_782_, 2, v_type_594_);
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_784_, 0, v_a_774_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v_value_595_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 2);
lean_ctor_set(v___x_776_, 0, v___x_785_);
v___x_787_ = v___x_776_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
v___y_724_ = v___y_770_;
v___y_725_ = v_a_774_;
v___y_726_ = v___y_769_;
v___y_727_ = v___x_781_;
v___y_728_ = v___y_771_;
v___y_729_ = v___y_772_;
v___y_730_ = v___f_778_;
v___y_731_ = v___x_787_;
goto v___jp_723_;
}
}
else
{
lean_del_object(v___x_776_);
v___y_752_ = v___y_770_;
v___y_753_ = v_a_774_;
v___y_754_ = v___y_769_;
v___y_755_ = v___y_771_;
v___y_756_ = v___y_772_;
v___y_757_ = v___f_778_;
goto v___jp_751_;
}
}
else
{
lean_del_object(v___x_776_);
lean_dec_ref(v_env_672_);
v___y_752_ = v___y_770_;
v___y_753_ = v_a_774_;
v___y_754_ = v___y_769_;
v___y_755_ = v___y_771_;
v___y_756_ = v___y_772_;
v___y_757_ = v___f_778_;
goto v___jp_751_;
}
}
}
v___jp_790_:
{
lean_object* v___x_796_; 
v___x_796_ = lean_st_ref_take(v___y_795_);
if (v_logWrites_675_ == 0)
{
lean_object* v_env_797_; lean_object* v_nextMacroScope_798_; lean_object* v_ngen_799_; lean_object* v_auxDeclNGen_800_; lean_object* v_traceState_801_; lean_object* v_recordedDeps_802_; lean_object* v_messages_803_; lean_object* v_infoState_804_; lean_object* v_snapshotTasks_805_; lean_object* v___x_806_; 
v_env_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc_ref(v_env_797_);
v_nextMacroScope_798_ = lean_ctor_get(v___x_796_, 1);
lean_inc(v_nextMacroScope_798_);
v_ngen_799_ = lean_ctor_get(v___x_796_, 2);
lean_inc_ref(v_ngen_799_);
v_auxDeclNGen_800_ = lean_ctor_get(v___x_796_, 3);
lean_inc_ref(v_auxDeclNGen_800_);
v_traceState_801_ = lean_ctor_get(v___x_796_, 4);
lean_inc_ref(v_traceState_801_);
v_recordedDeps_802_ = lean_ctor_get(v___x_796_, 6);
lean_inc_ref(v_recordedDeps_802_);
v_messages_803_ = lean_ctor_get(v___x_796_, 7);
lean_inc_ref(v_messages_803_);
v_infoState_804_ = lean_ctor_get(v___x_796_, 8);
lean_inc_ref(v_infoState_804_);
v_snapshotTasks_805_ = lean_ctor_get(v___x_796_, 9);
lean_inc_ref(v_snapshotTasks_805_);
lean_dec(v___x_796_);
v___x_806_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_673_, v_env_797_, v___y_791_, v_asyncMode_674_, v___x_677_, v___y_793_);
v___y_639_ = v___y_794_;
v_nextMacroScope_640_ = v_nextMacroScope_798_;
v_ngen_641_ = v_ngen_799_;
v_auxDeclNGen_642_ = v_auxDeclNGen_800_;
v_traceState_643_ = v_traceState_801_;
v_recordedDeps_644_ = v_recordedDeps_802_;
v_messages_645_ = v_messages_803_;
v_infoState_646_ = v_infoState_804_;
v_snapshotTasks_647_ = v_snapshotTasks_805_;
v___y_648_ = v___y_792_;
v___y_649_ = v___y_795_;
v___y_650_ = v___x_806_;
goto v___jp_638_;
}
else
{
lean_object* v_env_807_; lean_object* v_nextMacroScope_808_; lean_object* v_ngen_809_; lean_object* v_auxDeclNGen_810_; lean_object* v_traceState_811_; lean_object* v_recordedDeps_812_; lean_object* v_messages_813_; lean_object* v_infoState_814_; lean_object* v_snapshotTasks_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_env_807_ = lean_ctor_get(v___x_796_, 0);
lean_inc_ref(v_env_807_);
v_nextMacroScope_808_ = lean_ctor_get(v___x_796_, 1);
lean_inc(v_nextMacroScope_808_);
v_ngen_809_ = lean_ctor_get(v___x_796_, 2);
lean_inc_ref(v_ngen_809_);
v_auxDeclNGen_810_ = lean_ctor_get(v___x_796_, 3);
lean_inc_ref(v_auxDeclNGen_810_);
v_traceState_811_ = lean_ctor_get(v___x_796_, 4);
lean_inc_ref(v_traceState_811_);
v_recordedDeps_812_ = lean_ctor_get(v___x_796_, 6);
lean_inc_ref(v_recordedDeps_812_);
v_messages_813_ = lean_ctor_get(v___x_796_, 7);
lean_inc_ref(v_messages_813_);
v_infoState_814_ = lean_ctor_get(v___x_796_, 8);
lean_inc_ref(v_infoState_814_);
v_snapshotTasks_815_ = lean_ctor_get(v___x_796_, 9);
lean_inc_ref(v_snapshotTasks_815_);
lean_dec(v___x_796_);
v___x_816_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_673_, v_env_807_);
lean_dec_ref(v_env_807_);
v___x_817_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_673_, v___x_816_, v___y_791_, v_asyncMode_674_, v___x_677_, v___y_793_);
v___y_639_ = v___y_794_;
v_nextMacroScope_640_ = v_nextMacroScope_808_;
v_ngen_641_ = v_ngen_809_;
v_auxDeclNGen_642_ = v_auxDeclNGen_810_;
v_traceState_643_ = v_traceState_811_;
v_recordedDeps_644_ = v_recordedDeps_812_;
v_messages_645_ = v_messages_813_;
v_infoState_646_ = v_infoState_814_;
v_snapshotTasks_647_ = v_snapshotTasks_815_;
v___y_648_ = v___y_792_;
v___y_649_ = v___y_795_;
v___y_650_ = v___x_817_;
goto v___jp_638_;
}
}
v___jp_818_:
{
if (v_inferRfl_598_ == 0)
{
v___y_791_ = v___y_819_;
v___y_792_ = v___y_820_;
v___y_793_ = v___y_821_;
v___y_794_ = v___y_823_;
v___y_795_ = v___y_825_;
goto v___jp_790_;
}
else
{
lean_object* v___x_826_; 
lean_inc(v___y_820_);
v___x_826_ = l_Lean_inferDefEqAttr(v___y_820_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_dec_ref_known(v___x_826_, 1);
v___y_791_ = v___y_819_;
v___y_792_ = v___y_820_;
v___y_793_ = v___y_821_;
v___y_794_ = v___y_823_;
v___y_795_ = v___y_825_;
goto v___jp_790_;
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
v___jp_835_:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_addDecl(v___y_839_, v_forceExpose_599_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_dec_ref_known(v___x_840_, 1);
if (v_defeq_600_ == 0)
{
v___y_819_ = v___y_836_;
v___y_820_ = v___y_837_;
v___y_821_ = v___y_838_;
v___y_822_ = v_a_601_;
v___y_823_ = v_a_602_;
v___y_824_ = v_a_603_;
v___y_825_ = v_a_604_;
goto v___jp_818_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = l_Lean_defeqAttr;
lean_inc(v___y_837_);
v___x_842_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3(v___x_841_, v___y_837_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_dec_ref_known(v___x_842_, 1);
v___y_819_ = v___y_836_;
v___y_820_ = v___y_837_;
v___y_821_ = v___y_838_;
v___y_822_ = v_a_601_;
v___y_823_ = v_a_602_;
v___y_824_ = v_a_603_;
v___y_825_ = v_a_604_;
goto v___jp_818_;
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
v_a_851_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_840_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_840_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
v___jp_859_:
{
uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_862_ = 1;
lean_inc_n(v___y_861_, 2);
v___x_863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_863_, 0, v___y_861_);
lean_ctor_set(v___x_863_, 1, v_levelParams_593_);
lean_ctor_set(v___x_863_, 2, v_type_594_);
v___x_864_ = lean_box(0);
v___x_865_ = 0;
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v___y_861_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_868_, 0, v___x_863_);
lean_ctor_set(v___x_868_, 1, v_value_595_);
lean_ctor_set(v___x_868_, 2, v___x_864_);
lean_ctor_set(v___x_868_, 3, v___x_867_);
lean_ctor_set_uint8(v___x_868_, sizeof(void*)*4, v___x_865_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
v___y_836_ = v___y_860_;
v___y_837_ = v___y_861_;
v___y_838_ = v___x_862_;
v___y_839_ = v___x_869_;
goto v___jp_835_;
}
v___jp_872_:
{
if (v___y_874_ == 0)
{
lean_dec(v___x_871_);
v___y_767_ = v___y_873_;
v___y_768_ = v___y_875_;
v___y_769_ = v___y_876_;
v___y_770_ = v___y_877_;
v___y_771_ = v___y_878_;
v___y_772_ = v___y_879_;
goto v___jp_766_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_inc_ref(v_type_594_);
v___x_880_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_880_, 0, v_type_594_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*1, v___x_870_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*1 + 1, v_defeq_600_);
v___x_881_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4___redArg(v___x_871_, v___x_880_);
lean_dec_ref_known(v___x_880_, 1);
lean_dec(v___x_871_);
if (lean_obj_tag(v___x_881_) == 1)
{
lean_object* v_val_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_892_; 
v_val_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_892_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_val_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_fst_886_; lean_object* v_snd_887_; uint8_t v___x_888_; 
v_fst_886_ = lean_ctor_get(v_val_882_, 0);
lean_inc(v_fst_886_);
v_snd_887_ = lean_ctor_get(v_val_882_, 1);
lean_inc(v_snd_887_);
lean_dec(v_val_882_);
v___x_888_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__5(v_levelParams_593_, v_snd_887_);
lean_dec(v_snd_887_);
if (v___x_888_ == 0)
{
lean_dec(v_fst_886_);
lean_del_object(v___x_884_);
v___y_767_ = v___y_873_;
v___y_768_ = v___y_875_;
v___y_769_ = v___y_876_;
v___y_770_ = v___y_877_;
v___y_771_ = v___y_878_;
v___y_772_ = v___y_879_;
goto v___jp_766_;
}
else
{
lean_object* v___x_890_; 
lean_dec(v___y_875_);
lean_dec_ref(v___y_873_);
lean_dec_ref(v_env_672_);
lean_dec_ref(v_value_595_);
lean_dec_ref(v_type_594_);
lean_dec(v_levelParams_593_);
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 0);
lean_ctor_set(v___x_884_, 0, v_fst_886_);
v___x_890_ = v___x_884_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_fst_886_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_dec(v___x_881_);
v___y_767_ = v___y_873_;
v___y_768_ = v___y_875_;
v___y_769_ = v___y_876_;
v___y_770_ = v___y_877_;
v___y_771_ = v___y_878_;
v___y_772_ = v___y_879_;
goto v___jp_766_;
}
}
}
v___jp_893_:
{
if (v_cache_597_ == 0)
{
lean_object* v___x_897_; lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_913_; 
lean_dec(v___x_871_);
v___x_897_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_896_, v_a_604_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_913_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_913_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_913_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___f_902_; uint8_t v___x_903_; 
lean_inc(v_levelParams_593_);
lean_inc(v_a_898_);
v___f_902_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_902_, 0, v_a_898_);
lean_closure_set(v___f_902_, 1, v_levelParams_593_);
lean_closure_set(v___f_902_, 2, v___y_895_);
lean_inc_ref(v_env_672_);
v___x_903_ = l_Lean_Environment_hasUnsafe(v_env_672_, v_type_594_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_Environment_hasUnsafe(v_env_672_, v_value_595_);
if (v___x_904_ == 0)
{
uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_905_ = 1;
lean_inc_n(v_a_898_, 2);
v___x_906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_906_, 0, v_a_898_);
lean_ctor_set(v___x_906_, 1, v_levelParams_593_);
lean_ctor_set(v___x_906_, 2, v_type_594_);
v___x_907_ = lean_box(0);
v___x_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_908_, 0, v_a_898_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_909_, 0, v___x_906_);
lean_ctor_set(v___x_909_, 1, v_value_595_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 2);
lean_ctor_set(v___x_900_, 0, v___x_909_);
v___x_911_ = v___x_900_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
v___y_836_ = v___f_902_;
v___y_837_ = v_a_898_;
v___y_838_ = v___x_905_;
v___y_839_ = v___x_911_;
goto v___jp_835_;
}
}
else
{
lean_del_object(v___x_900_);
v___y_860_ = v___f_902_;
v___y_861_ = v_a_898_;
goto v___jp_859_;
}
}
else
{
lean_del_object(v___x_900_);
lean_dec_ref(v_env_672_);
v___y_860_ = v___f_902_;
v___y_861_ = v_a_898_;
goto v___jp_859_;
}
}
}
else
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4___redArg(v___x_871_, v___y_895_);
if (lean_obj_tag(v___x_914_) == 1)
{
lean_object* v_val_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_925_; 
v_val_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_925_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_val_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_fst_919_; lean_object* v_snd_920_; uint8_t v___x_921_; 
v_fst_919_ = lean_ctor_get(v_val_915_, 0);
lean_inc(v_fst_919_);
v_snd_920_ = lean_ctor_get(v_val_915_, 1);
lean_inc(v_snd_920_);
lean_dec(v_val_915_);
v___x_921_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__5(v_levelParams_593_, v_snd_920_);
lean_dec(v_snd_920_);
if (v___x_921_ == 0)
{
lean_dec(v_fst_919_);
lean_del_object(v___x_917_);
v___y_873_ = v___y_895_;
v___y_874_ = v___y_894_;
v___y_875_ = v___y_896_;
v___y_876_ = v_a_601_;
v___y_877_ = v_a_602_;
v___y_878_ = v_a_603_;
v___y_879_ = v_a_604_;
goto v___jp_872_;
}
else
{
lean_object* v___x_923_; 
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___x_871_);
lean_dec_ref(v_env_672_);
lean_dec_ref(v_value_595_);
lean_dec_ref(v_type_594_);
lean_dec(v_levelParams_593_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
lean_ctor_set(v___x_917_, 0, v_fst_919_);
v___x_923_ = v___x_917_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_fst_919_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_dec(v___x_914_);
v___y_873_ = v___y_895_;
v___y_874_ = v___y_894_;
v___y_875_ = v___y_896_;
v___y_876_ = v_a_601_;
v___y_877_ = v_a_602_;
v___y_878_ = v_a_603_;
v___y_879_ = v_a_604_;
goto v___jp_872_;
}
}
}
v___jp_926_:
{
lean_object* v___x_928_; 
lean_inc_ref(v_type_594_);
v___x_928_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_928_, 0, v_type_594_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*1, v___y_927_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*1 + 1, v_defeq_600_);
if (lean_obj_tag(v_kind_x3f_596_) == 0)
{
lean_object* v___x_929_; 
v___x_929_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__1));
v___y_894_ = v___y_927_;
v___y_895_ = v___x_928_;
v___y_896_ = v___x_929_;
goto v___jp_893_;
}
else
{
lean_object* v_val_930_; 
v_val_930_ = lean_ctor_get(v_kind_x3f_596_, 0);
lean_inc(v_val_930_);
lean_dec_ref_known(v_kind_x3f_596_, 1);
v___y_894_ = v___y_927_;
v___y_895_ = v___x_928_;
v___y_896_ = v_val_930_;
goto v___jp_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_932_, lean_object* v_type_933_, lean_object* v_value_934_, lean_object* v_kind_x3f_935_, lean_object* v_cache_936_, lean_object* v_inferRfl_937_, lean_object* v_forceExpose_938_, lean_object* v_defeq_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
uint8_t v_cache_boxed_945_; uint8_t v_inferRfl_boxed_946_; uint8_t v_forceExpose_boxed_947_; uint8_t v_defeq_boxed_948_; lean_object* v_res_949_; 
v_cache_boxed_945_ = lean_unbox(v_cache_936_);
v_inferRfl_boxed_946_ = lean_unbox(v_inferRfl_937_);
v_forceExpose_boxed_947_ = lean_unbox(v_forceExpose_938_);
v_defeq_boxed_948_ = lean_unbox(v_defeq_939_);
v_res_949_ = l_Lean_Meta_mkAuxLemma(v_levelParams_932_, v_type_933_, v_value_934_, v_kind_x3f_935_, v_cache_boxed_945_, v_inferRfl_boxed_946_, v_forceExpose_boxed_947_, v_defeq_boxed_948_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_951_, v_x_952_, v_x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b2_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2___redArg___boxed(lean_object* v___dummy_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2___redArg();
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object* v_00_u03b2_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3___closed__2);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4(lean_object* v_00_u03b2_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4___redArg(v_x_964_, v_x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(lean_object* v_00_u03b2_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4(v_00_u03b2_967_, v_x_968_, v_x_969_);
lean_dec_ref(v_x_969_);
lean_dec_ref(v_x_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_971_, lean_object* v_x_972_, size_t v_x_973_, size_t v_x_974_, lean_object* v_x_975_, lean_object* v_x_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_972_, v_x_973_, v_x_974_, v_x_975_, v_x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
size_t v_x_7054__boxed_984_; size_t v_x_7055__boxed_985_; lean_object* v_res_986_; 
v_x_7054__boxed_984_ = lean_unbox_usize(v_x_980_);
lean_dec(v_x_980_);
v_x_7055__boxed_985_ = lean_unbox_usize(v_x_981_);
lean_dec(v_x_981_);
v_res_986_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_978_, v_x_979_, v_x_7054__boxed_984_, v_x_7055__boxed_985_, v_x_982_, v_x_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5(lean_object* v_00_u03b1_987_, lean_object* v_attrName_988_, lean_object* v_declName_989_, lean_object* v_asyncPrefix_x3f_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___redArg(v_attrName_988_, v_declName_989_, v_asyncPrefix_x3f_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5___boxed(lean_object* v_00_u03b1_997_, lean_object* v_attrName_998_, lean_object* v_declName_999_, lean_object* v_asyncPrefix_x3f_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5(v_00_u03b1_997_, v_attrName_998_, v_declName_999_, v_asyncPrefix_x3f_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object* v_00_u03b1_1007_, lean_object* v_attrName_1008_, lean_object* v_declName_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_attrName_1008_, v_declName_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_attrName_1017_, lean_object* v_declName_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(v_00_u03b1_1016_, v_attrName_1017_, v_declName_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8(lean_object* v_00_u03b2_1025_, lean_object* v_x_1026_, size_t v_x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8___redArg(v_x_1026_, v_x_1027_, v_x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_){
_start:
{
size_t v_x_7105__boxed_1034_; lean_object* v_res_1035_; 
v_x_7105__boxed_1034_ = lean_unbox_usize(v_x_1032_);
lean_dec(v_x_1032_);
v_res_1035_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8(v_00_u03b2_1030_, v_x_1031_, v_x_7105__boxed_1034_, v_x_1033_);
lean_dec_ref(v_x_1033_);
lean_dec_ref(v_x_1031_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1036_, lean_object* v_n_1037_, lean_object* v_k_1038_, lean_object* v_v_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_1037_, v_k_1038_, v_v_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1041_, size_t v_depth_1042_, lean_object* v_keys_1043_, lean_object* v_vals_1044_, lean_object* v_heq_1045_, lean_object* v_i_1046_, lean_object* v_entries_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_1042_, v_keys_1043_, v_vals_1044_, v_i_1046_, v_entries_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1049_, lean_object* v_depth_1050_, lean_object* v_keys_1051_, lean_object* v_vals_1052_, lean_object* v_heq_1053_, lean_object* v_i_1054_, lean_object* v_entries_1055_){
_start:
{
size_t v_depth_boxed_1056_; lean_object* v_res_1057_; 
v_depth_boxed_1056_ = lean_unbox_usize(v_depth_1050_);
lean_dec(v_depth_1050_);
v_res_1057_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_1049_, v_depth_boxed_1056_, v_keys_1051_, v_vals_1052_, v_heq_1053_, v_i_1054_, v_entries_1055_);
lean_dec_ref(v_vals_1052_);
lean_dec_ref(v_keys_1051_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1058_, lean_object* v_msg_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8___redArg(v_msg_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1066_, lean_object* v_msg_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__3_spec__5_spec__8(v_00_u03b1_1066_, v_msg_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1074_, lean_object* v_keys_1075_, lean_object* v_vals_1076_, lean_object* v_heq_1077_, lean_object* v_i_1078_, lean_object* v_k_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12___redArg(v_keys_1075_, v_vals_1076_, v_i_1078_, v_k_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1081_, lean_object* v_keys_1082_, lean_object* v_vals_1083_, lean_object* v_heq_1084_, lean_object* v_i_1085_, lean_object* v_k_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__4_spec__8_spec__12(v_00_u03b2_1081_, v_keys_1082_, v_vals_1083_, v_heq_1084_, v_i_1085_, v_k_1086_);
lean_dec_ref(v_k_1086_);
lean_dec_ref(v_vals_1083_);
lean_dec_ref(v_keys_1082_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__8___redArg(v_x_1089_, v_x_1090_, v_x_1091_, v_x_1092_);
return v___x_1093_;
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
