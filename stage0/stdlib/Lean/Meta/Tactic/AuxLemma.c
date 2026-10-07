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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_x_118_, lean_object* v_x_119_){
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
v___x_150_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_n_146_, v___x_149_, v_k_147_, v_v_148_);
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
size_t v_x_5585__boxed_255_; size_t v_x_5586__boxed_256_; lean_object* v_res_257_; 
v_x_5585__boxed_255_ = lean_unbox_usize(v_x_251_);
lean_dec(v_x_251_);
v_x_5586__boxed_256_ = lean_unbox_usize(v_x_252_);
lean_dec(v_x_252_);
v_res_257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_250_, v_x_5585__boxed_255_, v_x_5586__boxed_256_, v_x_253_, v_x_254_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(lean_object* v_msgData_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___x_277_; lean_object* v_env_278_; uint8_t v___x_279_; lean_object* v_env_280_; lean_object* v___x_281_; lean_object* v_toCold_282_; lean_object* v_mctx_283_; lean_object* v_lctx_284_; lean_object* v_options_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_277_ = lean_st_ref_get(v___y_275_);
v_env_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc_ref(v_env_278_);
lean_dec(v___x_277_);
v___x_279_ = 0;
v_env_280_ = l_Lean_Environment_setRecordingDeps(v_env_278_, v___x_279_);
v___x_281_ = lean_st_ref_get(v___y_273_);
v_toCold_282_ = lean_ctor_get(v___y_274_, 0);
v_mctx_283_ = lean_ctor_get(v___x_281_, 0);
lean_inc_ref(v_mctx_283_);
lean_dec(v___x_281_);
v_lctx_284_ = lean_ctor_get(v___y_272_, 2);
v_options_285_ = lean_ctor_get(v_toCold_282_, 2);
lean_inc_ref(v_options_285_);
lean_inc_ref(v_lctx_284_);
v___x_286_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_286_, 0, v_env_280_);
lean_ctor_set(v___x_286_, 1, v_mctx_283_);
lean_ctor_set(v___x_286_, 2, v_lctx_284_);
lean_ctor_set(v___x_286_, 3, v_options_285_);
v___x_287_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_msgData_271_);
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_msgData_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msgData_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(lean_object* v_msg_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_ref_302_; lean_object* v___x_303_; lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_312_; 
v_ref_302_ = lean_ctor_get(v___y_299_, 2);
v___x_303_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msg_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
v_a_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_312_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_310_; 
lean_inc(v_ref_302_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_ref_302_);
lean_ctor_set(v___x_308_, 1, v_a_304_);
if (v_isShared_307_ == 0)
{
lean_ctor_set_tag(v___x_306_, 1);
lean_ctor_set(v___x_306_, 0, v___x_308_);
v___x_310_ = v___x_306_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0));
v___x_322_ = l_Lean_stringToMessageData(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2));
v___x_325_ = l_Lean_stringToMessageData(v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4));
v___x_328_ = l_Lean_stringToMessageData(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6));
v___x_331_ = l_Lean_stringToMessageData(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8));
v___x_334_ = l_Lean_stringToMessageData(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(lean_object* v_attrName_335_, lean_object* v_declName_336_, lean_object* v_asyncPrefix_x3f_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___y_344_; 
if (lean_obj_tag(v_asyncPrefix_x3f_337_) == 0)
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_MessageData_nil;
v___y_344_ = v___x_357_;
goto v___jp_343_;
}
else
{
lean_object* v_val_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_val_358_ = lean_ctor_get(v_asyncPrefix_x3f_337_, 0);
lean_inc(v_val_358_);
lean_dec_ref_known(v_asyncPrefix_x3f_337_, 1);
v___x_359_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7);
v___x_360_ = l_Lean_MessageData_ofName(v_val_358_);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9);
v___x_363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___y_344_ = v___x_363_;
goto v___jp_343_;
}
v___jp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_345_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_346_ = l_Lean_MessageData_ofName(v_attrName_335_);
v___x_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = 0;
v___x_351_ = l_Lean_MessageData_ofConstName(v_declName_336_, v___x_350_);
v___x_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_349_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___y_344_);
v___x_356_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_355_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object* v_attrName_364_, lean_object* v_declName_365_, lean_object* v_asyncPrefix_x3f_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_364_, v_declName_365_, v_asyncPrefix_x3f_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___lam__0(lean_object* v_addEntryFn_373_, lean_object* v_decl_374_, lean_object* v_s_375_){
_start:
{
lean_object* v_importedEntries_376_; lean_object* v_state_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_385_; 
v_importedEntries_376_ = lean_ctor_get(v_s_375_, 0);
v_state_377_ = lean_ctor_get(v_s_375_, 1);
v_isSharedCheck_385_ = !lean_is_exclusive(v_s_375_);
if (v_isSharedCheck_385_ == 0)
{
v___x_379_ = v_s_375_;
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_state_377_);
lean_inc(v_importedEntries_376_);
lean_dec(v_s_375_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_state_381_; lean_object* v___x_383_; 
v_state_381_ = lean_apply_2(v_addEntryFn_373_, v_state_377_, v_decl_374_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v_state_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_importedEntries_376_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_state_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(lean_object* v_attrName_389_, lean_object* v_declName_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_396_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_397_ = l_Lean_MessageData_ofName(v_attrName_389_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = 0;
v___x_402_ = l_Lean_MessageData_ofConstName(v_declName_390_, v___x_401_);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_400_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_405_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___boxed(lean_object* v_attrName_407_, lean_object* v_declName_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_407_, v_declName_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_420_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
lean_ctor_set(v___x_420_, 2, v___x_419_);
lean_ctor_set(v___x_420_, 3, v___x_419_);
lean_ctor_set(v___x_420_, 4, v___x_419_);
lean_ctor_set(v___x_420_, 5, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object* v_attr_421_, lean_object* v_decl_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___x_483_; lean_object* v_env_484_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___x_499_; 
v___x_483_ = lean_st_ref_get(v___y_426_);
v_env_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_env_484_);
lean_dec(v___x_483_);
v___x_499_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_484_, v_decl_422_);
if (lean_obj_tag(v___x_499_) == 0)
{
v___y_486_ = v___y_423_;
v___y_487_ = v___y_424_;
v___y_488_ = v___y_425_;
v___y_489_ = v___y_426_;
goto v___jp_485_;
}
else
{
lean_object* v_attr_500_; lean_object* v_toAttributeImplCore_501_; lean_object* v_name_502_; lean_object* v___x_503_; 
lean_dec_ref_known(v___x_499_, 1);
lean_dec_ref(v_env_484_);
v_attr_500_ = lean_ctor_get(v_attr_421_, 0);
lean_inc_ref(v_attr_500_);
lean_dec_ref(v_attr_421_);
v_toAttributeImplCore_501_ = lean_ctor_get(v_attr_500_, 0);
lean_inc_ref(v_toAttributeImplCore_501_);
lean_dec_ref(v_attr_500_);
v_name_502_ = lean_ctor_get(v_toAttributeImplCore_501_, 1);
lean_inc(v_name_502_);
lean_dec_ref(v_toAttributeImplCore_501_);
v___x_503_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_name_502_, v_decl_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
return v___x_503_;
}
v___jp_428_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_mctx_444_; lean_object* v_zetaDeltaFVarIds_445_; lean_object* v_postponed_446_; lean_object* v_diag_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_458_; 
v___x_440_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_441_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_441_, 0, v___y_439_);
lean_ctor_set(v___x_441_, 1, v___y_437_);
lean_ctor_set(v___x_441_, 2, v___y_436_);
lean_ctor_set(v___x_441_, 3, v___y_434_);
lean_ctor_set(v___x_441_, 4, v___y_431_);
lean_ctor_set(v___x_441_, 5, v___x_440_);
lean_ctor_set(v___x_441_, 6, v___y_435_);
lean_ctor_set(v___x_441_, 7, v___y_432_);
lean_ctor_set(v___x_441_, 8, v___y_433_);
lean_ctor_set(v___x_441_, 9, v___y_430_);
v___x_442_ = lean_st_ref_put(v___y_438_, v___x_441_);
v___x_443_ = lean_st_ref_take(v___y_429_);
v_mctx_444_ = lean_ctor_get(v___x_443_, 0);
v_zetaDeltaFVarIds_445_ = lean_ctor_get(v___x_443_, 2);
v_postponed_446_ = lean_ctor_get(v___x_443_, 3);
v_diag_447_ = lean_ctor_get(v___x_443_, 4);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v___x_443_, 1);
lean_dec(v_unused_459_);
v___x_449_ = v___x_443_;
v_isShared_450_ = v_isSharedCheck_458_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_diag_447_);
lean_inc(v_postponed_446_);
lean_inc(v_zetaDeltaFVarIds_445_);
lean_inc(v_mctx_444_);
lean_dec(v___x_443_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_458_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_451_ = lean_box(0);
v___x_452_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_mctx_444_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_zetaDeltaFVarIds_445_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_postponed_446_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v_diag_447_);
v___x_454_ = v_reuseFailAlloc_457_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_st_ref_put(v___y_429_, v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_451_);
return v___x_456_;
}
}
}
v___jp_460_:
{
lean_object* v___x_463_; lean_object* v_ext_464_; lean_object* v_toEnvExtension_465_; lean_object* v_env_466_; lean_object* v_nextMacroScope_467_; lean_object* v_ngen_468_; lean_object* v_auxDeclNGen_469_; lean_object* v_traceState_470_; lean_object* v_recordedDeps_471_; lean_object* v_messages_472_; lean_object* v_infoState_473_; lean_object* v_snapshotTasks_474_; lean_object* v_addEntryFn_475_; lean_object* v_asyncMode_476_; uint8_t v_logWrites_477_; lean_object* v___f_478_; uint8_t v___x_479_; 
v___x_463_ = lean_st_ref_take(v___y_462_);
v_ext_464_ = lean_ctor_get(v_attr_421_, 1);
lean_inc_ref(v_ext_464_);
lean_dec_ref(v_attr_421_);
v_toEnvExtension_465_ = lean_ctor_get(v_ext_464_, 0);
lean_inc_ref(v_toEnvExtension_465_);
v_env_466_ = lean_ctor_get(v___x_463_, 0);
lean_inc_ref(v_env_466_);
v_nextMacroScope_467_ = lean_ctor_get(v___x_463_, 1);
lean_inc(v_nextMacroScope_467_);
v_ngen_468_ = lean_ctor_get(v___x_463_, 2);
lean_inc_ref(v_ngen_468_);
v_auxDeclNGen_469_ = lean_ctor_get(v___x_463_, 3);
lean_inc_ref(v_auxDeclNGen_469_);
v_traceState_470_ = lean_ctor_get(v___x_463_, 4);
lean_inc_ref(v_traceState_470_);
v_recordedDeps_471_ = lean_ctor_get(v___x_463_, 6);
lean_inc_ref(v_recordedDeps_471_);
v_messages_472_ = lean_ctor_get(v___x_463_, 7);
lean_inc_ref(v_messages_472_);
v_infoState_473_ = lean_ctor_get(v___x_463_, 8);
lean_inc_ref(v_infoState_473_);
v_snapshotTasks_474_ = lean_ctor_get(v___x_463_, 9);
lean_inc_ref(v_snapshotTasks_474_);
lean_dec(v___x_463_);
v_addEntryFn_475_ = lean_ctor_get(v_ext_464_, 3);
lean_inc(v_addEntryFn_475_);
lean_dec_ref(v_ext_464_);
v_asyncMode_476_ = lean_ctor_get(v_toEnvExtension_465_, 2);
lean_inc(v_asyncMode_476_);
v_logWrites_477_ = lean_ctor_get_uint8(v_toEnvExtension_465_, sizeof(void*)*6);
lean_inc(v_decl_422_);
v___f_478_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_478_, 0, v_addEntryFn_475_);
lean_closure_set(v___f_478_, 1, v_decl_422_);
v___x_479_ = 1;
if (v_logWrites_477_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_465_, v_env_466_, v___f_478_, v_asyncMode_476_, v_decl_422_, v___x_479_);
lean_dec(v_asyncMode_476_);
v___y_429_ = v___y_461_;
v___y_430_ = v_snapshotTasks_474_;
v___y_431_ = v_traceState_470_;
v___y_432_ = v_messages_472_;
v___y_433_ = v_infoState_473_;
v___y_434_ = v_auxDeclNGen_469_;
v___y_435_ = v_recordedDeps_471_;
v___y_436_ = v_ngen_468_;
v___y_437_ = v_nextMacroScope_467_;
v___y_438_ = v___y_462_;
v___y_439_ = v___x_480_;
goto v___jp_428_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_inc_ref(v_toEnvExtension_465_);
v___x_481_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_465_, v_env_466_);
lean_dec_ref(v_env_466_);
v___x_482_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_465_, v___x_481_, v___f_478_, v_asyncMode_476_, v_decl_422_, v___x_479_);
lean_dec(v_asyncMode_476_);
v___y_429_ = v___y_461_;
v___y_430_ = v_snapshotTasks_474_;
v___y_431_ = v_traceState_470_;
v___y_432_ = v_messages_472_;
v___y_433_ = v_infoState_473_;
v___y_434_ = v_auxDeclNGen_469_;
v___y_435_ = v_recordedDeps_471_;
v___y_436_ = v_ngen_468_;
v___y_437_ = v_nextMacroScope_467_;
v___y_438_ = v___y_462_;
v___y_439_ = v___x_482_;
goto v___jp_428_;
}
}
v___jp_485_:
{
lean_object* v_ext_490_; lean_object* v_toEnvExtension_491_; lean_object* v_attr_492_; lean_object* v_asyncMode_493_; uint8_t v___x_494_; 
v_ext_490_ = lean_ctor_get(v_attr_421_, 1);
v_toEnvExtension_491_ = lean_ctor_get(v_ext_490_, 0);
v_attr_492_ = lean_ctor_get(v_attr_421_, 0);
v_asyncMode_493_ = lean_ctor_get(v_toEnvExtension_491_, 2);
lean_inc(v_decl_422_);
lean_inc_ref(v_env_484_);
v___x_494_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_484_, v_decl_422_, v_asyncMode_493_);
if (v___x_494_ == 0)
{
lean_object* v_toAttributeImplCore_495_; lean_object* v_name_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_inc_ref(v_attr_492_);
lean_dec_ref(v_attr_421_);
v_toAttributeImplCore_495_ = lean_ctor_get(v_attr_492_, 0);
lean_inc_ref(v_toAttributeImplCore_495_);
lean_dec_ref(v_attr_492_);
v_name_496_ = lean_ctor_get(v_toAttributeImplCore_495_, 1);
lean_inc(v_name_496_);
lean_dec_ref(v_toAttributeImplCore_495_);
v___x_497_ = l_Lean_Environment_asyncPrefix_x3f(v_env_484_);
v___x_498_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_name_496_, v_decl_422_, v___x_497_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
return v___x_498_;
}
else
{
lean_dec_ref(v_env_484_);
v___y_461_ = v___y_487_;
v___y_462_ = v___y_489_;
goto v___jp_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object* v_attr_504_, lean_object* v_decl_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v_attr_504_, v_decl_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(lean_object* v_keys_512_, lean_object* v_vals_513_, lean_object* v_i_514_, lean_object* v_k_515_){
_start:
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_array_get_size(v_keys_512_);
v___x_517_ = lean_nat_dec_lt(v_i_514_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
lean_dec(v_i_514_);
v___x_518_ = lean_box(0);
return v___x_518_;
}
else
{
lean_object* v_k_x27_519_; uint8_t v___x_520_; 
v_k_x27_519_ = lean_array_fget_borrowed(v_keys_512_, v_i_514_);
v___x_520_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_k_515_, v_k_x27_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_nat_add(v_i_514_, v___x_521_);
lean_dec(v_i_514_);
v_i_514_ = v___x_522_;
goto _start;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_array_fget_borrowed(v_vals_513_, v_i_514_);
lean_dec(v_i_514_);
lean_inc(v___x_524_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_keys_526_, lean_object* v_vals_527_, lean_object* v_i_528_, lean_object* v_k_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_526_, v_vals_527_, v_i_528_, v_k_529_);
lean_dec_ref(v_k_529_);
lean_dec_ref(v_vals_527_);
lean_dec_ref(v_keys_526_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(lean_object* v_x_531_, size_t v_x_532_, lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v_es_534_; lean_object* v___x_535_; size_t v___x_536_; size_t v___x_537_; lean_object* v_j_538_; lean_object* v___x_539_; 
v_es_534_ = lean_ctor_get(v_x_531_, 0);
v___x_535_ = lean_box(2);
v___x_536_ = ((size_t)31ULL);
v___x_537_ = lean_usize_land(v_x_532_, v___x_536_);
v_j_538_ = lean_usize_to_nat(v___x_537_);
v___x_539_ = lean_array_get_borrowed(v___x_535_, v_es_534_, v_j_538_);
lean_dec(v_j_538_);
switch(lean_obj_tag(v___x_539_))
{
case 0:
{
lean_object* v_key_540_; lean_object* v_val_541_; uint8_t v___x_542_; 
v_key_540_ = lean_ctor_get(v___x_539_, 0);
v_val_541_ = lean_ctor_get(v___x_539_, 1);
v___x_542_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_533_, v_key_540_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
v___x_543_ = lean_box(0);
return v___x_543_;
}
else
{
lean_object* v___x_544_; 
lean_inc(v_val_541_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v_val_541_);
return v___x_544_;
}
}
case 1:
{
lean_object* v_node_545_; size_t v___x_546_; size_t v___x_547_; 
v_node_545_ = lean_ctor_get(v___x_539_, 0);
v___x_546_ = ((size_t)5ULL);
v___x_547_ = lean_usize_shift_right(v_x_532_, v___x_546_);
v_x_531_ = v_node_545_;
v_x_532_ = v___x_547_;
goto _start;
}
default: 
{
lean_object* v___x_549_; 
v___x_549_ = lean_box(0);
return v___x_549_;
}
}
}
else
{
lean_object* v_ks_550_; lean_object* v_vs_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_ks_550_ = lean_ctor_get(v_x_531_, 0);
v_vs_551_ = lean_ctor_get(v_x_531_, 1);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_ks_550_, v_vs_551_, v___x_552_, v_x_533_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
size_t v_x_6156__boxed_557_; lean_object* v_res_558_; 
v_x_6156__boxed_557_ = lean_unbox_usize(v_x_555_);
lean_dec(v_x_555_);
v_res_558_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_554_, v_x_6156__boxed_557_, v_x_556_);
lean_dec_ref(v_x_556_);
lean_dec_ref(v_x_554_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
uint64_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v___x_561_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_560_);
v___x_562_ = lean_uint64_to_usize(v___x_561_);
v___x_563_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_559_, v___x_562_, v_x_560_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg___boxed(lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_564_, v_x_565_);
lean_dec_ref(v_x_565_);
lean_dec_ref(v_x_564_);
return v_res_566_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
if (lean_obj_tag(v_x_568_) == 0)
{
uint8_t v___x_569_; 
v___x_569_ = 1;
return v___x_569_;
}
else
{
uint8_t v___x_570_; 
v___x_570_ = 0;
return v___x_570_;
}
}
else
{
if (lean_obj_tag(v_x_568_) == 0)
{
uint8_t v___x_571_; 
v___x_571_ = 0;
return v___x_571_;
}
else
{
lean_object* v_head_572_; lean_object* v_tail_573_; lean_object* v_head_574_; lean_object* v_tail_575_; uint8_t v___x_576_; 
v_head_572_ = lean_ctor_get(v_x_567_, 0);
v_tail_573_ = lean_ctor_get(v_x_567_, 1);
v_head_574_ = lean_ctor_get(v_x_568_, 0);
v_tail_575_ = lean_ctor_get(v_x_568_, 1);
v___x_576_ = lean_name_eq(v_head_572_, v_head_574_);
if (v___x_576_ == 0)
{
return v___x_576_;
}
else
{
v_x_567_ = v_tail_573_;
v_x_568_ = v_tail_575_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
uint8_t v_res_580_; lean_object* v_r_581_; 
v_res_580_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_x_578_, v_x_579_);
lean_dec(v_x_579_);
lean_dec(v_x_578_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object* v_levelParams_585_, lean_object* v_type_586_, lean_object* v_value_587_, lean_object* v_kind_x3f_588_, uint8_t v_cache_589_, uint8_t v_inferRfl_590_, uint8_t v_forceExpose_591_, uint8_t v_defeq_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___y_599_; lean_object* v_nextMacroScope_600_; lean_object* v_ngen_601_; lean_object* v_auxDeclNGen_602_; lean_object* v_traceState_603_; lean_object* v_recordedDeps_604_; lean_object* v_messages_605_; lean_object* v_infoState_606_; lean_object* v_snapshotTasks_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v_nextMacroScope_631_; lean_object* v_ngen_632_; lean_object* v_auxDeclNGen_633_; lean_object* v_traceState_634_; lean_object* v_recordedDeps_635_; lean_object* v_messages_636_; lean_object* v_infoState_637_; lean_object* v_snapshotTasks_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_env_664_; lean_object* v___x_665_; lean_object* v_asyncMode_666_; uint8_t v_logWrites_667_; uint8_t v_isExporting_668_; lean_object* v___x_669_; lean_object* v___y_671_; uint8_t v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_699_; lean_object* v___y_700_; uint8_t v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; uint8_t v___y_750_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; uint8_t v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_805_; uint8_t v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; uint8_t v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_846_; lean_object* v___y_847_; uint8_t v___y_848_; uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___y_865_; uint8_t v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_886_; uint8_t v___y_887_; lean_object* v___y_888_; uint8_t v___y_907_; 
v___x_662_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_663_ = lean_st_ref_get(v_a_596_);
v_env_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc_ref_n(v_env_664_, 2);
lean_dec(v___x_663_);
v___x_665_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_666_ = lean_ctor_get(v___x_665_, 2);
v_logWrites_667_ = lean_ctor_get_uint8(v___x_665_, sizeof(void*)*6);
v_isExporting_668_ = lean_ctor_get_uint8(v_env_664_, sizeof(void*)*13);
v___x_669_ = lean_box(0);
v___x_862_ = 0;
v___x_863_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_662_, v___x_665_, v_env_664_, v_asyncMode_666_, v___x_669_, v___x_862_);
if (v_isExporting_668_ == 0)
{
uint8_t v___x_911_; 
v___x_911_ = 1;
v___y_907_ = v___x_911_;
goto v___jp_906_;
}
else
{
v___y_907_ = v___x_862_;
goto v___jp_906_;
}
v___jp_598_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_mctx_615_; lean_object* v_zetaDeltaFVarIds_616_; lean_object* v_postponed_617_; lean_object* v_diag_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_628_; 
v___x_611_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_612_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_612_, 0, v___y_610_);
lean_ctor_set(v___x_612_, 1, v_nextMacroScope_600_);
lean_ctor_set(v___x_612_, 2, v_ngen_601_);
lean_ctor_set(v___x_612_, 3, v_auxDeclNGen_602_);
lean_ctor_set(v___x_612_, 4, v_traceState_603_);
lean_ctor_set(v___x_612_, 5, v___x_611_);
lean_ctor_set(v___x_612_, 6, v_recordedDeps_604_);
lean_ctor_set(v___x_612_, 7, v_messages_605_);
lean_ctor_set(v___x_612_, 8, v_infoState_606_);
lean_ctor_set(v___x_612_, 9, v_snapshotTasks_607_);
v___x_613_ = lean_st_ref_put(v___y_609_, v___x_612_);
v___x_614_ = lean_st_ref_take(v___y_608_);
v_mctx_615_ = lean_ctor_get(v___x_614_, 0);
v_zetaDeltaFVarIds_616_ = lean_ctor_get(v___x_614_, 2);
v_postponed_617_ = lean_ctor_get(v___x_614_, 3);
v_diag_618_ = lean_ctor_get(v___x_614_, 4);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v___x_614_, 1);
lean_dec(v_unused_629_);
v___x_620_ = v___x_614_;
v_isShared_621_ = v_isSharedCheck_628_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_diag_618_);
lean_inc(v_postponed_617_);
lean_inc(v_zetaDeltaFVarIds_616_);
lean_inc(v_mctx_615_);
lean_dec(v___x_614_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_628_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_mctx_615_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_zetaDeltaFVarIds_616_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_postponed_617_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_diag_618_);
v___x_624_ = v_reuseFailAlloc_627_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_st_ref_put(v___y_608_, v___x_624_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___y_599_);
return v___x_626_;
}
}
}
v___jp_630_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v_mctx_647_; lean_object* v_zetaDeltaFVarIds_648_; lean_object* v_postponed_649_; lean_object* v_diag_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_660_; 
v___x_643_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_644_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_644_, 0, v___y_642_);
lean_ctor_set(v___x_644_, 1, v_nextMacroScope_631_);
lean_ctor_set(v___x_644_, 2, v_ngen_632_);
lean_ctor_set(v___x_644_, 3, v_auxDeclNGen_633_);
lean_ctor_set(v___x_644_, 4, v_traceState_634_);
lean_ctor_set(v___x_644_, 5, v___x_643_);
lean_ctor_set(v___x_644_, 6, v_recordedDeps_635_);
lean_ctor_set(v___x_644_, 7, v_messages_636_);
lean_ctor_set(v___x_644_, 8, v_infoState_637_);
lean_ctor_set(v___x_644_, 9, v_snapshotTasks_638_);
v___x_645_ = lean_st_ref_put(v___y_641_, v___x_644_);
v___x_646_ = lean_st_ref_take(v___y_640_);
v_mctx_647_ = lean_ctor_get(v___x_646_, 0);
v_zetaDeltaFVarIds_648_ = lean_ctor_get(v___x_646_, 2);
v_postponed_649_ = lean_ctor_get(v___x_646_, 3);
v_diag_650_ = lean_ctor_get(v___x_646_, 4);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_646_, 1);
lean_dec(v_unused_661_);
v___x_652_ = v___x_646_;
v_isShared_653_ = v_isSharedCheck_660_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_diag_650_);
lean_inc(v_postponed_649_);
lean_inc(v_zetaDeltaFVarIds_648_);
lean_inc(v_mctx_647_);
lean_dec(v___x_646_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_660_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_654_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_mctx_647_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_zetaDeltaFVarIds_648_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_postponed_649_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v_diag_650_);
v___x_656_ = v_reuseFailAlloc_659_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_st_ref_put(v___y_640_, v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___y_639_);
return v___x_658_;
}
}
}
v___jp_670_:
{
lean_object* v___x_676_; 
v___x_676_ = lean_st_ref_take(v___y_675_);
if (v_logWrites_667_ == 0)
{
lean_object* v_env_677_; lean_object* v_nextMacroScope_678_; lean_object* v_ngen_679_; lean_object* v_auxDeclNGen_680_; lean_object* v_traceState_681_; lean_object* v_recordedDeps_682_; lean_object* v_messages_683_; lean_object* v_infoState_684_; lean_object* v_snapshotTasks_685_; lean_object* v___x_686_; 
v_env_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref(v_env_677_);
v_nextMacroScope_678_ = lean_ctor_get(v___x_676_, 1);
lean_inc(v_nextMacroScope_678_);
v_ngen_679_ = lean_ctor_get(v___x_676_, 2);
lean_inc_ref(v_ngen_679_);
v_auxDeclNGen_680_ = lean_ctor_get(v___x_676_, 3);
lean_inc_ref(v_auxDeclNGen_680_);
v_traceState_681_ = lean_ctor_get(v___x_676_, 4);
lean_inc_ref(v_traceState_681_);
v_recordedDeps_682_ = lean_ctor_get(v___x_676_, 6);
lean_inc_ref(v_recordedDeps_682_);
v_messages_683_ = lean_ctor_get(v___x_676_, 7);
lean_inc_ref(v_messages_683_);
v_infoState_684_ = lean_ctor_get(v___x_676_, 8);
lean_inc_ref(v_infoState_684_);
v_snapshotTasks_685_ = lean_ctor_get(v___x_676_, 9);
lean_inc_ref(v_snapshotTasks_685_);
lean_dec(v___x_676_);
v___x_686_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_665_, v_env_677_, v___y_671_, v_asyncMode_666_, v___x_669_, v___y_672_);
v_nextMacroScope_631_ = v_nextMacroScope_678_;
v_ngen_632_ = v_ngen_679_;
v_auxDeclNGen_633_ = v_auxDeclNGen_680_;
v_traceState_634_ = v_traceState_681_;
v_recordedDeps_635_ = v_recordedDeps_682_;
v_messages_636_ = v_messages_683_;
v_infoState_637_ = v_infoState_684_;
v_snapshotTasks_638_ = v_snapshotTasks_685_;
v___y_639_ = v___y_673_;
v___y_640_ = v___y_674_;
v___y_641_ = v___y_675_;
v___y_642_ = v___x_686_;
goto v___jp_630_;
}
else
{
lean_object* v_env_687_; lean_object* v_nextMacroScope_688_; lean_object* v_ngen_689_; lean_object* v_auxDeclNGen_690_; lean_object* v_traceState_691_; lean_object* v_recordedDeps_692_; lean_object* v_messages_693_; lean_object* v_infoState_694_; lean_object* v_snapshotTasks_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_env_687_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref(v_env_687_);
v_nextMacroScope_688_ = lean_ctor_get(v___x_676_, 1);
lean_inc(v_nextMacroScope_688_);
v_ngen_689_ = lean_ctor_get(v___x_676_, 2);
lean_inc_ref(v_ngen_689_);
v_auxDeclNGen_690_ = lean_ctor_get(v___x_676_, 3);
lean_inc_ref(v_auxDeclNGen_690_);
v_traceState_691_ = lean_ctor_get(v___x_676_, 4);
lean_inc_ref(v_traceState_691_);
v_recordedDeps_692_ = lean_ctor_get(v___x_676_, 6);
lean_inc_ref(v_recordedDeps_692_);
v_messages_693_ = lean_ctor_get(v___x_676_, 7);
lean_inc_ref(v_messages_693_);
v_infoState_694_ = lean_ctor_get(v___x_676_, 8);
lean_inc_ref(v_infoState_694_);
v_snapshotTasks_695_ = lean_ctor_get(v___x_676_, 9);
lean_inc_ref(v_snapshotTasks_695_);
lean_dec(v___x_676_);
v___x_696_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_665_, v_env_687_);
lean_dec_ref(v_env_687_);
v___x_697_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_665_, v___x_696_, v___y_671_, v_asyncMode_666_, v___x_669_, v___y_672_);
v_nextMacroScope_631_ = v_nextMacroScope_688_;
v_ngen_632_ = v_ngen_689_;
v_auxDeclNGen_633_ = v_auxDeclNGen_690_;
v_traceState_634_ = v_traceState_691_;
v_recordedDeps_635_ = v_recordedDeps_692_;
v_messages_636_ = v_messages_693_;
v_infoState_637_ = v_infoState_694_;
v_snapshotTasks_638_ = v_snapshotTasks_695_;
v___y_639_ = v___y_673_;
v___y_640_ = v___y_674_;
v___y_641_ = v___y_675_;
v___y_642_ = v___x_697_;
goto v___jp_630_;
}
}
v___jp_698_:
{
if (v_inferRfl_590_ == 0)
{
v___y_671_ = v___y_699_;
v___y_672_ = v___y_701_;
v___y_673_ = v___y_700_;
v___y_674_ = v___y_703_;
v___y_675_ = v___y_705_;
goto v___jp_670_;
}
else
{
lean_object* v___x_706_; 
lean_inc(v___y_700_);
v___x_706_ = l_Lean_inferDefEqAttr(v___y_700_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_dec_ref_known(v___x_706_, 1);
v___y_671_ = v___y_699_;
v___y_672_ = v___y_701_;
v___y_673_ = v___y_700_;
v___y_674_ = v___y_703_;
v___y_675_ = v___y_705_;
goto v___jp_670_;
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
v___jp_715_:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_addDecl(v___y_723_, v_forceExpose_591_, v___y_719_, v___y_718_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_dec_ref_known(v___x_724_, 1);
if (v_defeq_592_ == 0)
{
v___y_699_ = v___y_717_;
v___y_700_ = v___y_721_;
v___y_701_ = v___y_720_;
v___y_702_ = v___y_722_;
v___y_703_ = v___y_716_;
v___y_704_ = v___y_719_;
v___y_705_ = v___y_718_;
goto v___jp_698_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = l_Lean_defeqAttr;
lean_inc(v___y_721_);
v___x_726_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_725_, v___y_721_, v___y_722_, v___y_716_, v___y_719_, v___y_718_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_dec_ref_known(v___x_726_, 1);
v___y_699_ = v___y_717_;
v___y_700_ = v___y_721_;
v___y_701_ = v___y_720_;
v___y_702_ = v___y_722_;
v___y_703_ = v___y_716_;
v___y_704_ = v___y_719_;
v___y_705_ = v___y_718_;
goto v___jp_698_;
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v___y_721_);
lean_dec_ref(v___y_717_);
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v___y_721_);
lean_dec_ref(v___y_717_);
v_a_735_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_724_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_724_);
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
v___jp_743_:
{
uint8_t v___x_751_; 
v___x_751_ = 1;
if (v___y_750_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_inc_n(v___y_748_, 2);
v___x_752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_752_, 0, v___y_748_);
lean_ctor_set(v___x_752_, 1, v_levelParams_585_);
lean_ctor_set(v___x_752_, 2, v_type_586_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_754_, 0, v___y_748_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_755_, 0, v___x_752_);
lean_ctor_set(v___x_755_, 1, v_value_587_);
lean_ctor_set(v___x_755_, 2, v___x_754_);
v___x_756_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
v___y_716_ = v___y_744_;
v___y_717_ = v___y_747_;
v___y_718_ = v___y_746_;
v___y_719_ = v___y_745_;
v___y_720_ = v___x_751_;
v___y_721_ = v___y_748_;
v___y_722_ = v___y_749_;
v___y_723_ = v___x_756_;
goto v___jp_715_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_inc_n(v___y_748_, 2);
v___x_757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_757_, 0, v___y_748_);
lean_ctor_set(v___x_757_, 1, v_levelParams_585_);
lean_ctor_set(v___x_757_, 2, v_type_586_);
v___x_758_ = lean_box(0);
v___x_759_ = 0;
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_761_, 0, v___y_748_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_762_, 0, v___x_757_);
lean_ctor_set(v___x_762_, 1, v_value_587_);
lean_ctor_set(v___x_762_, 2, v___x_758_);
lean_ctor_set(v___x_762_, 3, v___x_761_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*4, v___x_759_);
v___x_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
v___y_716_ = v___y_744_;
v___y_717_ = v___y_747_;
v___y_718_ = v___y_746_;
v___y_719_ = v___y_745_;
v___y_720_ = v___x_751_;
v___y_721_ = v___y_748_;
v___y_722_ = v___y_749_;
v___y_723_ = v___x_763_;
goto v___jp_715_;
}
}
v___jp_764_:
{
lean_object* v___x_771_; lean_object* v_a_772_; lean_object* v___f_773_; uint8_t v___x_774_; 
v___x_771_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_766_, v___y_770_);
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc_n(v_a_772_, 2);
lean_dec_ref(v___x_771_);
lean_inc(v_levelParams_585_);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_773_, 0, v_a_772_);
lean_closure_set(v___f_773_, 1, v_levelParams_585_);
lean_closure_set(v___f_773_, 2, v___y_765_);
lean_inc_ref(v_env_664_);
v___x_774_ = l_Lean_Environment_hasUnsafe(v_env_664_, v_type_586_);
if (v___x_774_ == 0)
{
uint8_t v___x_775_; 
v___x_775_ = l_Lean_Environment_hasUnsafe(v_env_664_, v_value_587_);
v___y_744_ = v___y_768_;
v___y_745_ = v___y_769_;
v___y_746_ = v___y_770_;
v___y_747_ = v___f_773_;
v___y_748_ = v_a_772_;
v___y_749_ = v___y_767_;
v___y_750_ = v___x_775_;
goto v___jp_743_;
}
else
{
lean_dec_ref(v_env_664_);
v___y_744_ = v___y_768_;
v___y_745_ = v___y_769_;
v___y_746_ = v___y_770_;
v___y_747_ = v___f_773_;
v___y_748_ = v_a_772_;
v___y_749_ = v___y_767_;
v___y_750_ = v___x_774_;
goto v___jp_743_;
}
}
v___jp_776_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_st_ref_take(v___y_781_);
if (v_logWrites_667_ == 0)
{
lean_object* v_env_783_; lean_object* v_nextMacroScope_784_; lean_object* v_ngen_785_; lean_object* v_auxDeclNGen_786_; lean_object* v_traceState_787_; lean_object* v_recordedDeps_788_; lean_object* v_messages_789_; lean_object* v_infoState_790_; lean_object* v_snapshotTasks_791_; lean_object* v___x_792_; 
v_env_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc_ref(v_env_783_);
v_nextMacroScope_784_ = lean_ctor_get(v___x_782_, 1);
lean_inc(v_nextMacroScope_784_);
v_ngen_785_ = lean_ctor_get(v___x_782_, 2);
lean_inc_ref(v_ngen_785_);
v_auxDeclNGen_786_ = lean_ctor_get(v___x_782_, 3);
lean_inc_ref(v_auxDeclNGen_786_);
v_traceState_787_ = lean_ctor_get(v___x_782_, 4);
lean_inc_ref(v_traceState_787_);
v_recordedDeps_788_ = lean_ctor_get(v___x_782_, 6);
lean_inc_ref(v_recordedDeps_788_);
v_messages_789_ = lean_ctor_get(v___x_782_, 7);
lean_inc_ref(v_messages_789_);
v_infoState_790_ = lean_ctor_get(v___x_782_, 8);
lean_inc_ref(v_infoState_790_);
v_snapshotTasks_791_ = lean_ctor_get(v___x_782_, 9);
lean_inc_ref(v_snapshotTasks_791_);
lean_dec(v___x_782_);
v___x_792_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_665_, v_env_783_, v___y_779_, v_asyncMode_666_, v___x_669_, v___y_777_);
v___y_599_ = v___y_778_;
v_nextMacroScope_600_ = v_nextMacroScope_784_;
v_ngen_601_ = v_ngen_785_;
v_auxDeclNGen_602_ = v_auxDeclNGen_786_;
v_traceState_603_ = v_traceState_787_;
v_recordedDeps_604_ = v_recordedDeps_788_;
v_messages_605_ = v_messages_789_;
v_infoState_606_ = v_infoState_790_;
v_snapshotTasks_607_ = v_snapshotTasks_791_;
v___y_608_ = v___y_780_;
v___y_609_ = v___y_781_;
v___y_610_ = v___x_792_;
goto v___jp_598_;
}
else
{
lean_object* v_env_793_; lean_object* v_nextMacroScope_794_; lean_object* v_ngen_795_; lean_object* v_auxDeclNGen_796_; lean_object* v_traceState_797_; lean_object* v_recordedDeps_798_; lean_object* v_messages_799_; lean_object* v_infoState_800_; lean_object* v_snapshotTasks_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_env_793_ = lean_ctor_get(v___x_782_, 0);
lean_inc_ref(v_env_793_);
v_nextMacroScope_794_ = lean_ctor_get(v___x_782_, 1);
lean_inc(v_nextMacroScope_794_);
v_ngen_795_ = lean_ctor_get(v___x_782_, 2);
lean_inc_ref(v_ngen_795_);
v_auxDeclNGen_796_ = lean_ctor_get(v___x_782_, 3);
lean_inc_ref(v_auxDeclNGen_796_);
v_traceState_797_ = lean_ctor_get(v___x_782_, 4);
lean_inc_ref(v_traceState_797_);
v_recordedDeps_798_ = lean_ctor_get(v___x_782_, 6);
lean_inc_ref(v_recordedDeps_798_);
v_messages_799_ = lean_ctor_get(v___x_782_, 7);
lean_inc_ref(v_messages_799_);
v_infoState_800_ = lean_ctor_get(v___x_782_, 8);
lean_inc_ref(v_infoState_800_);
v_snapshotTasks_801_ = lean_ctor_get(v___x_782_, 9);
lean_inc_ref(v_snapshotTasks_801_);
lean_dec(v___x_782_);
v___x_802_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_665_, v_env_793_);
lean_dec_ref(v_env_793_);
v___x_803_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_665_, v___x_802_, v___y_779_, v_asyncMode_666_, v___x_669_, v___y_777_);
v___y_599_ = v___y_778_;
v_nextMacroScope_600_ = v_nextMacroScope_794_;
v_ngen_601_ = v_ngen_795_;
v_auxDeclNGen_602_ = v_auxDeclNGen_796_;
v_traceState_603_ = v_traceState_797_;
v_recordedDeps_604_ = v_recordedDeps_798_;
v_messages_605_ = v_messages_799_;
v_infoState_606_ = v_infoState_800_;
v_snapshotTasks_607_ = v_snapshotTasks_801_;
v___y_608_ = v___y_780_;
v___y_609_ = v___y_781_;
v___y_610_ = v___x_803_;
goto v___jp_598_;
}
}
v___jp_804_:
{
if (v_inferRfl_590_ == 0)
{
v___y_777_ = v___y_806_;
v___y_778_ = v___y_805_;
v___y_779_ = v___y_807_;
v___y_780_ = v___y_809_;
v___y_781_ = v___y_811_;
goto v___jp_776_;
}
else
{
lean_object* v___x_812_; 
lean_inc(v___y_805_);
v___x_812_ = l_Lean_inferDefEqAttr(v___y_805_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_dec_ref_known(v___x_812_, 1);
v___y_777_ = v___y_806_;
v___y_778_ = v___y_805_;
v___y_779_ = v___y_807_;
v___y_780_ = v___y_809_;
v___y_781_ = v___y_811_;
goto v___jp_776_;
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v___y_807_);
lean_dec(v___y_805_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
v___jp_821_:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_addDecl(v___y_825_, v_forceExpose_591_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_dec_ref_known(v___x_826_, 1);
if (v_defeq_592_ == 0)
{
v___y_805_ = v___y_823_;
v___y_806_ = v___y_822_;
v___y_807_ = v___y_824_;
v___y_808_ = v_a_593_;
v___y_809_ = v_a_594_;
v___y_810_ = v_a_595_;
v___y_811_ = v_a_596_;
goto v___jp_804_;
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = l_Lean_defeqAttr;
lean_inc(v___y_823_);
v___x_828_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_827_, v___y_823_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_dec_ref_known(v___x_828_, 1);
v___y_805_ = v___y_823_;
v___y_806_ = v___y_822_;
v___y_807_ = v___y_824_;
v___y_808_ = v_a_593_;
v___y_809_ = v_a_594_;
v___y_810_ = v_a_595_;
v___y_811_ = v_a_596_;
goto v___jp_804_;
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
v_a_837_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_826_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_826_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
v___jp_845_:
{
uint8_t v___x_849_; 
v___x_849_ = 1;
if (v___y_848_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
lean_inc_n(v___y_846_, 2);
v___x_850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_850_, 0, v___y_846_);
lean_ctor_set(v___x_850_, 1, v_levelParams_585_);
lean_ctor_set(v___x_850_, 2, v_type_586_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_852_, 0, v___y_846_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_853_, 0, v___x_850_);
lean_ctor_set(v___x_853_, 1, v_value_587_);
lean_ctor_set(v___x_853_, 2, v___x_852_);
v___x_854_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
v___y_822_ = v___x_849_;
v___y_823_ = v___y_846_;
v___y_824_ = v___y_847_;
v___y_825_ = v___x_854_;
goto v___jp_821_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_inc_n(v___y_846_, 2);
v___x_855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_855_, 0, v___y_846_);
lean_ctor_set(v___x_855_, 1, v_levelParams_585_);
lean_ctor_set(v___x_855_, 2, v_type_586_);
v___x_856_ = lean_box(0);
v___x_857_ = 0;
v___x_858_ = lean_box(0);
v___x_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_859_, 0, v___y_846_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_860_, 0, v___x_855_);
lean_ctor_set(v___x_860_, 1, v_value_587_);
lean_ctor_set(v___x_860_, 2, v___x_856_);
lean_ctor_set(v___x_860_, 3, v___x_859_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*4, v___x_857_);
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
v___y_822_ = v___x_849_;
v___y_823_ = v___y_846_;
v___y_824_ = v___y_847_;
v___y_825_ = v___x_861_;
goto v___jp_821_;
}
}
v___jp_864_:
{
if (v___y_866_ == 0)
{
lean_dec(v___x_863_);
v___y_765_ = v___y_865_;
v___y_766_ = v___y_867_;
v___y_767_ = v___y_868_;
v___y_768_ = v___y_869_;
v___y_769_ = v___y_870_;
v___y_770_ = v___y_871_;
goto v___jp_764_;
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_inc_ref(v_type_586_);
v___x_872_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_872_, 0, v_type_586_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*1, v___x_862_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*1 + 1, v_defeq_592_);
v___x_873_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_863_, v___x_872_);
lean_dec_ref_known(v___x_872_, 1);
lean_dec(v___x_863_);
if (lean_obj_tag(v___x_873_) == 1)
{
lean_object* v_val_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_884_; 
v_val_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_884_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_884_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_val_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_884_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_fst_878_; lean_object* v_snd_879_; uint8_t v___x_880_; 
v_fst_878_ = lean_ctor_get(v_val_874_, 0);
lean_inc(v_fst_878_);
v_snd_879_ = lean_ctor_get(v_val_874_, 1);
lean_inc(v_snd_879_);
lean_dec(v_val_874_);
v___x_880_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_585_, v_snd_879_);
lean_dec(v_snd_879_);
if (v___x_880_ == 0)
{
lean_dec(v_fst_878_);
lean_del_object(v___x_876_);
v___y_765_ = v___y_865_;
v___y_766_ = v___y_867_;
v___y_767_ = v___y_868_;
v___y_768_ = v___y_869_;
v___y_769_ = v___y_870_;
v___y_770_ = v___y_871_;
goto v___jp_764_;
}
else
{
lean_object* v___x_882_; 
lean_dec(v___y_867_);
lean_dec_ref(v___y_865_);
lean_dec_ref(v_env_664_);
lean_dec_ref(v_value_587_);
lean_dec_ref(v_type_586_);
lean_dec(v_levelParams_585_);
if (v_isShared_877_ == 0)
{
lean_ctor_set_tag(v___x_876_, 0);
lean_ctor_set(v___x_876_, 0, v_fst_878_);
v___x_882_ = v___x_876_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_fst_878_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_dec(v___x_873_);
v___y_765_ = v___y_865_;
v___y_766_ = v___y_867_;
v___y_767_ = v___y_868_;
v___y_768_ = v___y_869_;
v___y_769_ = v___y_870_;
v___y_770_ = v___y_871_;
goto v___jp_764_;
}
}
}
v___jp_885_:
{
if (v_cache_589_ == 0)
{
lean_object* v___x_889_; lean_object* v_a_890_; lean_object* v___f_891_; uint8_t v___x_892_; 
lean_dec(v___x_863_);
v___x_889_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_888_, v_a_596_);
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc_n(v_a_890_, 2);
lean_dec_ref(v___x_889_);
lean_inc(v_levelParams_585_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_891_, 0, v_a_890_);
lean_closure_set(v___f_891_, 1, v_levelParams_585_);
lean_closure_set(v___f_891_, 2, v___y_886_);
lean_inc_ref(v_env_664_);
v___x_892_ = l_Lean_Environment_hasUnsafe(v_env_664_, v_type_586_);
if (v___x_892_ == 0)
{
uint8_t v___x_893_; 
v___x_893_ = l_Lean_Environment_hasUnsafe(v_env_664_, v_value_587_);
v___y_846_ = v_a_890_;
v___y_847_ = v___f_891_;
v___y_848_ = v___x_893_;
goto v___jp_845_;
}
else
{
lean_dec_ref(v_env_664_);
v___y_846_ = v_a_890_;
v___y_847_ = v___f_891_;
v___y_848_ = v___x_892_;
goto v___jp_845_;
}
}
else
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_863_, v___y_886_);
if (lean_obj_tag(v___x_894_) == 1)
{
lean_object* v_val_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_905_; 
v_val_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_905_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_905_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_val_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_905_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_fst_899_; lean_object* v_snd_900_; uint8_t v___x_901_; 
v_fst_899_ = lean_ctor_get(v_val_895_, 0);
lean_inc(v_fst_899_);
v_snd_900_ = lean_ctor_get(v_val_895_, 1);
lean_inc(v_snd_900_);
lean_dec(v_val_895_);
v___x_901_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_585_, v_snd_900_);
lean_dec(v_snd_900_);
if (v___x_901_ == 0)
{
lean_dec(v_fst_899_);
lean_del_object(v___x_897_);
v___y_865_ = v___y_886_;
v___y_866_ = v___y_887_;
v___y_867_ = v___y_888_;
v___y_868_ = v_a_593_;
v___y_869_ = v_a_594_;
v___y_870_ = v_a_595_;
v___y_871_ = v_a_596_;
goto v___jp_864_;
}
else
{
lean_object* v___x_903_; 
lean_dec(v___y_888_);
lean_dec_ref(v___y_886_);
lean_dec(v___x_863_);
lean_dec_ref(v_env_664_);
lean_dec_ref(v_value_587_);
lean_dec_ref(v_type_586_);
lean_dec(v_levelParams_585_);
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 0);
lean_ctor_set(v___x_897_, 0, v_fst_899_);
v___x_903_ = v___x_897_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_fst_899_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
lean_dec(v___x_894_);
v___y_865_ = v___y_886_;
v___y_866_ = v___y_887_;
v___y_867_ = v___y_888_;
v___y_868_ = v_a_593_;
v___y_869_ = v_a_594_;
v___y_870_ = v_a_595_;
v___y_871_ = v_a_596_;
goto v___jp_864_;
}
}
}
v___jp_906_:
{
lean_object* v___x_908_; 
lean_inc_ref(v_type_586_);
v___x_908_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_908_, 0, v_type_586_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*1, v___y_907_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*1 + 1, v_defeq_592_);
if (lean_obj_tag(v_kind_x3f_588_) == 0)
{
lean_object* v___x_909_; 
v___x_909_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__1));
v___y_886_ = v___x_908_;
v___y_887_ = v___y_907_;
v___y_888_ = v___x_909_;
goto v___jp_885_;
}
else
{
lean_object* v_val_910_; 
v_val_910_ = lean_ctor_get(v_kind_x3f_588_, 0);
lean_inc(v_val_910_);
lean_dec_ref_known(v_kind_x3f_588_, 1);
v___y_886_ = v___x_908_;
v___y_887_ = v___y_907_;
v___y_888_ = v_val_910_;
goto v___jp_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_912_, lean_object* v_type_913_, lean_object* v_value_914_, lean_object* v_kind_x3f_915_, lean_object* v_cache_916_, lean_object* v_inferRfl_917_, lean_object* v_forceExpose_918_, lean_object* v_defeq_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
uint8_t v_cache_boxed_925_; uint8_t v_inferRfl_boxed_926_; uint8_t v_forceExpose_boxed_927_; uint8_t v_defeq_boxed_928_; lean_object* v_res_929_; 
v_cache_boxed_925_ = lean_unbox(v_cache_916_);
v_inferRfl_boxed_926_ = lean_unbox(v_inferRfl_917_);
v_forceExpose_boxed_927_ = lean_unbox(v_forceExpose_918_);
v_defeq_boxed_928_ = lean_unbox(v_defeq_919_);
v_res_929_ = l_Lean_Meta_mkAuxLemma(v_levelParams_912_, v_type_913_, v_value_914_, v_kind_x3f_915_, v_cache_boxed_925_, v_inferRfl_boxed_926_, v_forceExpose_boxed_927_, v_defeq_boxed_928_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_931_, v_x_932_, v_x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_00_u03b2_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_936_, v_x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_00_u03b2_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(v_00_u03b2_939_, v_x_940_, v_x_941_);
lean_dec_ref(v_x_941_);
lean_dec_ref(v_x_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, size_t v_x_945_, size_t v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_944_, v_x_945_, v_x_946_, v_x_947_, v_x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
size_t v_x_6805__boxed_956_; size_t v_x_6806__boxed_957_; lean_object* v_res_958_; 
v_x_6805__boxed_956_ = lean_unbox_usize(v_x_952_);
lean_dec(v_x_952_);
v_x_6806__boxed_957_ = lean_unbox_usize(v_x_953_);
lean_dec(v_x_953_);
v_res_958_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_950_, v_x_951_, v_x_6805__boxed_956_, v_x_6806__boxed_957_, v_x_954_, v_x_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b1_959_, lean_object* v_attrName_960_, lean_object* v_declName_961_, lean_object* v_asyncPrefix_x3f_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_960_, v_declName_961_, v_asyncPrefix_x3f_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_969_, lean_object* v_attrName_970_, lean_object* v_declName_971_, lean_object* v_asyncPrefix_x3f_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b1_969_, v_attrName_970_, v_declName_971_, v_asyncPrefix_x3f_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(lean_object* v_00_u03b1_979_, lean_object* v_attrName_980_, lean_object* v_declName_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_980_, v_declName_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___boxed(lean_object* v_00_u03b1_988_, lean_object* v_attrName_989_, lean_object* v_declName_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(v_00_u03b1_988_, v_attrName_989_, v_declName_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object* v_00_u03b2_997_, lean_object* v_x_998_, size_t v_x_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_998_, v_x_999_, v_x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
size_t v_x_6856__boxed_1006_; lean_object* v_res_1007_; 
v_x_6856__boxed_1006_ = lean_unbox_usize(v_x_1004_);
lean_dec(v_x_1004_);
v_res_1007_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(v_00_u03b2_1002_, v_x_1003_, v_x_6856__boxed_1006_, v_x_1005_);
lean_dec_ref(v_x_1005_);
lean_dec_ref(v_x_1003_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1008_, lean_object* v_n_1009_, lean_object* v_k_1010_, lean_object* v_v_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_1009_, v_k_1010_, v_v_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1013_, size_t v_depth_1014_, lean_object* v_keys_1015_, lean_object* v_vals_1016_, lean_object* v_heq_1017_, lean_object* v_i_1018_, lean_object* v_entries_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_1014_, v_keys_1015_, v_vals_1016_, v_i_1018_, v_entries_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1021_, lean_object* v_depth_1022_, lean_object* v_keys_1023_, lean_object* v_vals_1024_, lean_object* v_heq_1025_, lean_object* v_i_1026_, lean_object* v_entries_1027_){
_start:
{
size_t v_depth_boxed_1028_; lean_object* v_res_1029_; 
v_depth_boxed_1028_ = lean_unbox_usize(v_depth_1022_);
lean_dec(v_depth_1022_);
v_res_1029_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_1021_, v_depth_boxed_1028_, v_keys_1023_, v_vals_1024_, v_heq_1025_, v_i_1026_, v_entries_1027_);
lean_dec_ref(v_vals_1024_);
lean_dec_ref(v_keys_1023_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_1030_, lean_object* v_msg_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1038_, lean_object* v_msg_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b1_1038_, v_msg_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1046_, lean_object* v_keys_1047_, lean_object* v_vals_1048_, lean_object* v_heq_1049_, lean_object* v_i_1050_, lean_object* v_k_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_1047_, v_vals_1048_, v_i_1050_, v_k_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1053_, lean_object* v_keys_1054_, lean_object* v_vals_1055_, lean_object* v_heq_1056_, lean_object* v_i_1057_, lean_object* v_k_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(v_00_u03b2_1053_, v_keys_1054_, v_vals_1055_, v_heq_1056_, v_i_1057_, v_k_1058_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_vals_1055_);
lean_dec_ref(v_keys_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_x_1061_, v_x_1062_, v_x_1063_, v_x_1064_);
return v___x_1065_;
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
