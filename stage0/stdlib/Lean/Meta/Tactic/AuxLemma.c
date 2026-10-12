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
uint8_t l_Lean_Meta_instBEqAuxLemmaKey_beq(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Lean_Meta_instBEqAuxLemmaKey_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_12_;
v_res_12_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_1_, v_x_2_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqAuxLemmaKey_beq___boxed(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_13_, v_x_14_);
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
uint64_t l_Lean_Meta_instHashableAuxLemmaKey_hash(lean_object* v_x_19_){
_start:
{
lean_object* v_type_20_; uint8_t v_isPrivate_21_; uint8_t v_defeq_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; uint64_t v___y_27_; 
v_type_20_ = lean_ctor_get(v_x_19_, 0);
v_isPrivate_21_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*1);
v_defeq_22_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*1 + 1);
v___x_23_ = 0ULL;
v___x_24_ = l_Lean_Expr_hash(v_type_20_);
v___x_25_ = lean_uint64_mix_hash(v___x_23_, v___x_24_);
if (v_isPrivate_21_ == 0)
{
uint64_t v___x_33_; 
v___x_33_ = 13ULL;
v___y_27_ = v___x_33_;
goto v___jp_26_;
}
else
{
uint64_t v___x_34_; 
v___x_34_ = 11ULL;
v___y_27_ = v___x_34_;
goto v___jp_26_;
}
v___jp_26_:
{
uint64_t v___x_28_; 
v___x_28_ = lean_uint64_mix_hash(v___x_25_, v___y_27_);
if (v_defeq_22_ == 0)
{
uint64_t v___x_29_; uint64_t v___x_30_; 
v___x_29_ = 13ULL;
v___x_30_ = lean_uint64_mix_hash(v___x_28_, v___x_29_);
return v___x_30_;
}
else
{
uint64_t v___x_31_; uint64_t v___x_32_; 
v___x_31_ = 11ULL;
v___x_32_ = lean_uint64_mix_hash(v___x_28_, v___x_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_instHashableAuxLemmaKey_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_19_ = stack[0].m_obj;
uint64_t v_res_35_;
v_res_35_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_19_);
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableAuxLemmaKey_hash___boxed(lean_object* v_x_36_){
_start:
{
uint64_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_36_);
lean_dec_ref(v_x_36_);
v_r_38_ = lean_box_uint64(v_res_37_);
return v_r_38_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas_default(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
return v___x_45_;
}
}
lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(lean_object* v___x_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_46_);
return v___x_48_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_46_ = stack[0].m_obj;
lean_object* v_res_49_;
v_res_49_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(v___x_46_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object* v___x_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(v___x_50_);
return v_res_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_53_; lean_object* v___f_54_; 
v___x_53_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1);
v___f_54_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_54_, 0, v___x_53_);
return v___f_54_;
}
}
lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; 
v___f_63_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_);
v___x_64_ = lean_box(0);
v___x_65_ = lean_box(1);
v___x_66_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_));
v___x_67_ = 0;
v___x_68_ = l_Lean_registerEnvExtension___redArg(v___f_63_, v___x_64_, v___x_65_, v___x_66_, v___x_67_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_69_;
v_res_69_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
return v_res_71_;
}
}
lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(lean_object* v_kind_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v_auxDeclNGen_76_; lean_object* v___x_77_; lean_object* v_env_78_; lean_object* v___x_79_; lean_object* v_fst_80_; lean_object* v_snd_81_; lean_object* v___x_82_; lean_object* v_env_83_; lean_object* v_nextMacroScope_84_; lean_object* v_ngen_85_; lean_object* v_traceState_86_; lean_object* v_cache_87_; lean_object* v_recordedDeps_88_; lean_object* v_messages_89_; lean_object* v_infoState_90_; lean_object* v_snapshotTasks_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_100_; 
v___x_75_ = lean_st_ref_get(v___y_73_);
v_auxDeclNGen_76_ = lean_ctor_get(v___x_75_, 3);
lean_inc_ref(v_auxDeclNGen_76_);
lean_dec(v___x_75_);
v___x_77_ = lean_st_ref_get(v___y_73_);
v_env_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc_ref(v_env_78_);
lean_dec(v___x_77_);
v___x_79_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_78_, v_auxDeclNGen_76_, v_kind_72_);
v_fst_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_fst_80_);
v_snd_81_ = lean_ctor_get(v___x_79_, 1);
lean_inc(v_snd_81_);
lean_dec_ref(v___x_79_);
v___x_82_ = lean_st_ref_take(v___y_73_);
v_env_83_ = lean_ctor_get(v___x_82_, 0);
v_nextMacroScope_84_ = lean_ctor_get(v___x_82_, 1);
v_ngen_85_ = lean_ctor_get(v___x_82_, 2);
v_traceState_86_ = lean_ctor_get(v___x_82_, 4);
v_cache_87_ = lean_ctor_get(v___x_82_, 5);
v_recordedDeps_88_ = lean_ctor_get(v___x_82_, 6);
v_messages_89_ = lean_ctor_get(v___x_82_, 7);
v_infoState_90_ = lean_ctor_get(v___x_82_, 8);
v_snapshotTasks_91_ = lean_ctor_get(v___x_82_, 9);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_82_, 3);
lean_dec(v_unused_101_);
v___x_93_ = v___x_82_;
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_snapshotTasks_91_);
lean_inc(v_infoState_90_);
lean_inc(v_messages_89_);
lean_inc(v_recordedDeps_88_);
lean_inc(v_cache_87_);
lean_inc(v_traceState_86_);
lean_inc(v_ngen_85_);
lean_inc(v_nextMacroScope_84_);
lean_inc(v_env_83_);
lean_dec(v___x_82_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 3, v_snd_81_);
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_env_83_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_nextMacroScope_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_ngen_85_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_snd_81_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v_traceState_86_);
lean_ctor_set(v_reuseFailAlloc_99_, 5, v_cache_87_);
lean_ctor_set(v_reuseFailAlloc_99_, 6, v_recordedDeps_88_);
lean_ctor_set(v_reuseFailAlloc_99_, 7, v_messages_89_);
lean_ctor_set(v_reuseFailAlloc_99_, 8, v_infoState_90_);
lean_ctor_set(v_reuseFailAlloc_99_, 9, v_snapshotTasks_91_);
v___x_96_ = v_reuseFailAlloc_99_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_st_ref_put(v___y_73_, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_fst_80_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_72_ = stack[0].m_obj;
lean_object* v___y_73_ = stack[1].m_obj;
lean_object* v_res_102_;
v_res_102_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_72_, v___y_73_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg___boxed(lean_object* v_kind_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_103_, v___y_104_);
lean_dec(v___y_104_);
return v_res_106_;
}
}
lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(lean_object* v_kind_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_107_, v___y_111_);
return v___x_113_;
}
}
LEAN_EXPORT void l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_107_ = stack[0].m_obj;
lean_object* v___y_108_ = stack[1].m_obj;
lean_object* v___y_109_ = stack[2].m_obj;
lean_object* v___y_110_ = stack[3].m_obj;
lean_object* v___y_111_ = stack[4].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(v_kind_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___boxed(lean_object* v_kind_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(v_kind_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_ks_126_; lean_object* v_vs_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_151_; 
v_ks_126_ = lean_ctor_get(v_x_122_, 0);
v_vs_127_ = lean_ctor_get(v_x_122_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_122_);
if (v_isSharedCheck_151_ == 0)
{
v___x_129_ = v_x_122_;
v_isShared_130_ = v_isSharedCheck_151_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_vs_127_);
lean_inc(v_ks_126_);
lean_dec(v_x_122_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_151_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_array_get_size(v_ks_126_);
v___x_132_ = lean_nat_dec_lt(v_x_123_, v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec(v_x_123_);
v___x_133_ = lean_array_push(v_ks_126_, v_x_124_);
v___x_134_ = lean_array_push(v_vs_127_, v_x_125_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_134_);
lean_ctor_set(v___x_129_, 0, v___x_133_);
v___x_136_ = v___x_129_;
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
else
{
lean_object* v_k_x27_138_; uint8_t v___x_139_; 
v_k_x27_138_ = lean_array_fget_borrowed(v_ks_126_, v_x_123_);
v___x_139_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_124_, v_k_x27_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_141_; 
if (v_isShared_130_ == 0)
{
v___x_141_ = v___x_129_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_ks_126_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_vs_127_);
v___x_141_ = v_reuseFailAlloc_145_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = lean_nat_add(v_x_123_, v___x_142_);
lean_dec(v_x_123_);
v_x_122_ = v___x_141_;
v_x_123_ = v___x_143_;
goto _start;
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_146_ = lean_array_fset(v_ks_126_, v_x_123_, v_x_124_);
v___x_147_ = lean_array_fset(v_vs_127_, v_x_123_, v_x_125_);
lean_dec(v_x_123_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_147_);
lean_ctor_set(v___x_129_, 0, v___x_146_);
v___x_149_ = v___x_129_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(lean_object* v_n_152_, lean_object* v_k_153_, lean_object* v_v_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_n_152_, v___x_155_, v_k_153_, v_v_154_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_157_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object* v_x_158_, size_t v_x_159_, size_t v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v_es_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v_j_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_es_163_ = lean_ctor_get(v_x_158_, 0);
v___x_164_ = ((size_t)31ULL);
v___x_165_ = lean_usize_land(v_x_159_, v___x_164_);
v_j_166_ = lean_usize_to_nat(v___x_165_);
v___x_167_ = lean_array_get_size(v_es_163_);
v___x_168_ = lean_nat_dec_lt(v_j_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_dec(v_j_166_);
lean_dec(v_x_162_);
lean_dec_ref(v_x_161_);
return v_x_158_;
}
else
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_207_; 
lean_inc_ref(v_es_163_);
v_isSharedCheck_207_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_x_158_, 0);
lean_dec(v_unused_208_);
v___x_170_ = v_x_158_;
v_isShared_171_ = v_isSharedCheck_207_;
goto v_resetjp_169_;
}
else
{
lean_dec(v_x_158_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_207_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_v_172_; lean_object* v___x_173_; lean_object* v_xs_x27_174_; lean_object* v___y_176_; 
v_v_172_ = lean_array_fget(v_es_163_, v_j_166_);
v___x_173_ = lean_box(0);
v_xs_x27_174_ = lean_array_fset(v_es_163_, v_j_166_, v___x_173_);
switch(lean_obj_tag(v_v_172_))
{
case 0:
{
lean_object* v_key_181_; lean_object* v_val_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_192_; 
v_key_181_ = lean_ctor_get(v_v_172_, 0);
v_val_182_ = lean_ctor_get(v_v_172_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_v_172_);
if (v_isSharedCheck_192_ == 0)
{
v___x_184_ = v_v_172_;
v_isShared_185_ = v_isSharedCheck_192_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_val_182_);
lean_inc(v_key_181_);
lean_dec(v_v_172_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_192_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_161_, v_key_181_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_del_object(v___x_184_);
v___x_187_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_181_, v_val_182_, v_x_161_, v_x_162_);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
v___y_176_ = v___x_188_;
goto v___jp_175_;
}
else
{
lean_object* v___x_190_; 
lean_dec(v_val_182_);
lean_dec(v_key_181_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v_x_162_);
lean_ctor_set(v___x_184_, 0, v_x_161_);
v___x_190_ = v___x_184_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_x_161_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_x_162_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
v___y_176_ = v___x_190_;
goto v___jp_175_;
}
}
}
}
case 1:
{
lean_object* v_node_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_205_; 
v_node_193_ = lean_ctor_get(v_v_172_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v_v_172_);
if (v_isSharedCheck_205_ == 0)
{
v___x_195_ = v_v_172_;
v_isShared_196_ = v_isSharedCheck_205_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_node_193_);
lean_dec(v_v_172_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_205_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_197_ = ((size_t)5ULL);
v___x_198_ = lean_usize_shift_right(v_x_159_, v___x_197_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_x_160_, v___x_199_);
v___x_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_node_193_, v___x_198_, v___x_200_, v_x_161_, v_x_162_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_201_);
v___x_203_ = v___x_195_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v___y_176_ = v___x_203_;
goto v___jp_175_;
}
}
}
default: 
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_x_161_);
lean_ctor_set(v___x_206_, 1, v_x_162_);
v___y_176_ = v___x_206_;
goto v___jp_175_;
}
}
v___jp_175_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_array_fset(v_xs_x27_174_, v_j_166_, v___y_176_);
lean_dec(v_j_166_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_177_);
v___x_179_ = v___x_170_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
else
{
lean_object* v_ks_209_; lean_object* v_vs_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_228_; 
v_ks_209_ = lean_ctor_get(v_x_158_, 0);
v_vs_210_ = lean_ctor_get(v_x_158_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_228_ == 0)
{
v___x_212_ = v_x_158_;
v_isShared_213_ = v_isSharedCheck_228_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_vs_210_);
lean_inc(v_ks_209_);
lean_dec(v_x_158_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_228_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_ks_209_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_vs_210_);
v___x_215_ = v_reuseFailAlloc_227_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v_newNode_216_; size_t v___x_217_; uint8_t v___x_218_; 
v_newNode_216_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v___x_215_, v_x_161_, v_x_162_);
v___x_217_ = ((size_t)7ULL);
v___x_218_ = lean_usize_dec_le(v___x_217_, v_x_160_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_216_);
v___x_220_ = lean_unsigned_to_nat(4u);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
lean_dec(v___x_219_);
if (v___x_221_ == 0)
{
lean_object* v_ks_222_; lean_object* v_vs_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_ks_222_ = lean_ctor_get(v_newNode_216_, 0);
lean_inc_ref(v_ks_222_);
v_vs_223_ = lean_ctor_get(v_newNode_216_, 1);
lean_inc_ref(v_vs_223_);
lean_dec_ref(v_newNode_216_);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0);
v___x_226_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_x_160_, v_ks_222_, v_vs_223_, v___x_224_, v___x_225_);
lean_dec_ref(v_vs_223_);
lean_dec_ref(v_ks_222_);
return v___x_226_;
}
else
{
return v_newNode_216_;
}
}
else
{
return v_newNode_216_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_158_ = stack[0].m_obj;
size_t v_x_159_ = stack[1].m_num;
size_t v_x_160_ = stack[2].m_num;
lean_object* v_x_161_ = stack[3].m_obj;
lean_object* v_x_162_ = stack[4].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_158_, v_x_159_, v_x_160_, v_x_161_, v_x_162_);
stack->m_obj
 = v_res_229_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t v_depth_230_, lean_object* v_keys_231_, lean_object* v_vals_232_, lean_object* v_i_233_, lean_object* v_entries_234_){
_start:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_array_get_size(v_keys_231_);
v___x_236_ = lean_nat_dec_lt(v_i_233_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v_i_233_);
return v_entries_234_;
}
else
{
lean_object* v_k_237_; lean_object* v_v_238_; uint64_t v___x_239_; size_t v_h_240_; size_t v___x_241_; lean_object* v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v_h_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_k_237_ = lean_array_fget_borrowed(v_keys_231_, v_i_233_);
v_v_238_ = lean_array_fget_borrowed(v_vals_232_, v_i_233_);
v___x_239_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_k_237_);
v_h_240_ = lean_uint64_to_usize(v___x_239_);
v___x_241_ = ((size_t)5ULL);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = ((size_t)1ULL);
v___x_244_ = lean_usize_sub(v_depth_230_, v___x_243_);
v___x_245_ = lean_usize_mul(v___x_241_, v___x_244_);
v_h_246_ = lean_usize_shift_right(v_h_240_, v___x_245_);
v___x_247_ = lean_nat_add(v_i_233_, v___x_242_);
lean_dec(v_i_233_);
lean_inc(v_v_238_);
lean_inc(v_k_237_);
v___x_248_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_entries_234_, v_h_246_, v_depth_230_, v_k_237_, v_v_238_);
v_i_233_ = v___x_247_;
v_entries_234_ = v___x_248_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_230_ = stack[0].m_num;
lean_object* v_keys_231_ = stack[1].m_obj;
lean_object* v_vals_232_ = stack[2].m_obj;
lean_object* v_i_233_ = stack[3].m_obj;
lean_object* v_entries_234_ = stack[4].m_obj;
lean_object* v_res_250_;
v_res_250_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_230_, v_keys_231_, v_vals_232_, v_i_233_, v_entries_234_);
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_251_, lean_object* v_keys_252_, lean_object* v_vals_253_, lean_object* v_i_254_, lean_object* v_entries_255_){
_start:
{
size_t v_depth_boxed_256_; lean_object* v_res_257_; 
v_depth_boxed_256_ = lean_unbox_usize(v_depth_251_);
lean_dec(v_depth_251_);
v_res_257_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_boxed_256_, v_keys_252_, v_vals_253_, v_i_254_, v_entries_255_);
lean_dec_ref(v_vals_253_);
lean_dec_ref(v_keys_252_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
size_t v_x_5647__boxed_263_; size_t v_x_5648__boxed_264_; lean_object* v_res_265_; 
v_x_5647__boxed_263_ = lean_unbox_usize(v_x_259_);
lean_dec(v_x_259_);
v_x_5648__boxed_264_ = lean_unbox_usize(v_x_260_);
lean_dec(v_x_260_);
v_res_265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_258_, v_x_5647__boxed_263_, v_x_5648__boxed_264_, v_x_261_, v_x_262_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object* v_x_266_, lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
uint64_t v___x_269_; size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
v___x_269_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_267_);
v___x_270_ = lean_uint64_to_usize(v___x_269_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_266_, v___x_270_, v___x_271_, v_x_267_, v_x_268_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object* v_a_273_, lean_object* v_levelParams_274_, lean_object* v___x_275_, lean_object* v_x_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v_a_273_);
lean_ctor_set(v___x_277_, 1, v_levelParams_274_);
v___x_278_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_276_, v___x_275_, v___x_277_);
return v___x_278_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; lean_object* v_env_286_; uint8_t v___x_287_; lean_object* v_env_288_; lean_object* v___x_289_; lean_object* v_toCold_290_; lean_object* v_mctx_291_; lean_object* v_lctx_292_; lean_object* v_options_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_285_ = lean_st_ref_get(v___y_283_);
v_env_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc_ref(v_env_286_);
lean_dec(v___x_285_);
v___x_287_ = 0;
v_env_288_ = l_Lean_Environment_setRecordingDeps(v_env_286_, v___x_287_);
v___x_289_ = lean_st_ref_get(v___y_281_);
v_toCold_290_ = lean_ctor_get(v___y_282_, 0);
v_mctx_291_ = lean_ctor_get(v___x_289_, 0);
lean_inc_ref(v_mctx_291_);
lean_dec(v___x_289_);
v_lctx_292_ = lean_ctor_get(v___y_280_, 2);
v_options_293_ = lean_ctor_get(v_toCold_290_, 2);
lean_inc_ref(v_options_293_);
lean_inc_ref(v_lctx_292_);
v___x_294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_294_, 0, v_env_288_);
lean_ctor_set(v___x_294_, 1, v_mctx_291_);
lean_ctor_set(v___x_294_, 2, v_lctx_292_);
lean_ctor_set(v___x_294_, 3, v_options_293_);
v___x_295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_msgData_279_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_279_ = stack[0].m_obj;
lean_object* v___y_280_ = stack[1].m_obj;
lean_object* v___y_281_ = stack[2].m_obj;
lean_object* v___y_282_ = stack[3].m_obj;
lean_object* v___y_283_ = stack[4].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msgData_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_msgData_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msgData_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_ref_311_; lean_object* v___x_312_; lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
v_ref_311_ = lean_ctor_get(v___y_308_, 2);
v___x_312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_spec__10(v_msg_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_321_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
lean_inc(v_ref_311_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_ref_311_);
lean_ctor_set(v___x_317_, 1, v_a_313_);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 1);
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_305_ = stack[0].m_obj;
lean_object* v___y_306_ = stack[1].m_obj;
lean_object* v___y_307_ = stack[2].m_obj;
lean_object* v___y_308_ = stack[3].m_obj;
lean_object* v___y_309_ = stack[4].m_obj;
lean_object* v_res_322_;
v_res_322_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
stack->m_obj
 = v_res_322_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_msg_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
return v_res_329_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__0));
v___x_332_ = l_Lean_stringToMessageData(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__2));
v___x_335_ = l_Lean_stringToMessageData(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__4));
v___x_338_ = l_Lean_stringToMessageData(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__6));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__8));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(lean_object* v_attrName_345_, lean_object* v_declName_346_, lean_object* v_asyncPrefix_x3f_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v___y_354_; 
if (lean_obj_tag(v_asyncPrefix_x3f_347_) == 0)
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_MessageData_nil;
v___y_354_ = v___x_367_;
goto v___jp_353_;
}
else
{
lean_object* v_val_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_val_368_ = lean_ctor_get(v_asyncPrefix_x3f_347_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v_asyncPrefix_x3f_347_, 1);
v___x_369_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__7);
v___x_370_ = l_Lean_MessageData_ofName(v_val_368_);
v___x_371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__9);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___y_354_ = v___x_373_;
goto v___jp_353_;
}
v___jp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_355_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_356_ = l_Lean_MessageData_ofName(v_attrName_345_);
v___x_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = 0;
v___x_361_ = l_Lean_MessageData_ofConstName(v_declName_346_, v___x_360_);
v___x_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_359_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__5);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___y_354_);
v___x_366_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_365_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
return v___x_366_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_345_ = stack[0].m_obj;
lean_object* v_declName_346_ = stack[1].m_obj;
lean_object* v_asyncPrefix_x3f_347_ = stack[2].m_obj;
lean_object* v___y_348_ = stack[3].m_obj;
lean_object* v___y_349_ = stack[4].m_obj;
lean_object* v___y_350_ = stack[5].m_obj;
lean_object* v___y_351_ = stack[6].m_obj;
lean_object* v_res_374_;
v_res_374_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_345_, v_declName_346_, v_asyncPrefix_x3f_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object* v_attrName_375_, lean_object* v_declName_376_, lean_object* v_asyncPrefix_x3f_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_375_, v_declName_376_, v_asyncPrefix_x3f_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___lam__0(lean_object* v_addEntryFn_384_, lean_object* v_decl_385_, lean_object* v_s_386_){
_start:
{
lean_object* v_importedEntries_387_; lean_object* v_state_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v_importedEntries_387_ = lean_ctor_get(v_s_386_, 0);
v_state_388_ = lean_ctor_get(v_s_386_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_s_386_);
if (v_isSharedCheck_396_ == 0)
{
v___x_390_ = v_s_386_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_state_388_);
lean_inc(v_importedEntries_387_);
lean_dec(v_s_386_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_state_392_; lean_object* v___x_394_; 
v_state_392_ = lean_apply_2(v_addEntryFn_384_, v_state_388_, v_decl_385_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v_state_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_importedEntries_387_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_state_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__0));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(lean_object* v_attrName_400_, lean_object* v_declName_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_407_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__1);
v___x_408_ = l_Lean_MessageData_ofName(v_attrName_400_);
v___x_409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___closed__3);
v___x_411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = 0;
v___x_413_ = l_Lean_MessageData_ofConstName(v_declName_401_, v___x_412_);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_411_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___closed__1);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v___x_416_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
return v___x_417_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_400_ = stack[0].m_obj;
lean_object* v_declName_401_ = stack[1].m_obj;
lean_object* v___y_402_ = stack[2].m_obj;
lean_object* v___y_403_ = stack[3].m_obj;
lean_object* v___y_404_ = stack[4].m_obj;
lean_object* v___y_405_ = stack[5].m_obj;
lean_object* v_res_418_;
v_res_418_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_400_, v_declName_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg___boxed(lean_object* v_attrName_419_, lean_object* v_declName_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_419_, v_declName_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_426_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__0);
v___x_432_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
lean_ctor_set(v___x_432_, 2, v___x_431_);
lean_ctor_set(v___x_432_, 3, v___x_431_);
lean_ctor_set(v___x_432_, 4, v___x_431_);
lean_ctor_set(v___x_432_, 5, v___x_431_);
return v___x_432_;
}
}
lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object* v_attr_433_, lean_object* v_decl_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___x_495_; lean_object* v_env_496_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___x_511_; 
v___x_495_ = lean_st_ref_get(v___y_438_);
v_env_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_env_496_);
lean_dec(v___x_495_);
v___x_511_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_496_, v_decl_434_);
if (lean_obj_tag(v___x_511_) == 0)
{
v___y_498_ = v___y_435_;
v___y_499_ = v___y_436_;
v___y_500_ = v___y_437_;
v___y_501_ = v___y_438_;
goto v___jp_497_;
}
else
{
lean_object* v_attr_512_; lean_object* v_toAttributeImplCore_513_; lean_object* v_name_514_; lean_object* v___x_515_; 
lean_dec_ref_known(v___x_511_, 1);
lean_dec_ref(v_env_496_);
v_attr_512_ = lean_ctor_get(v_attr_433_, 0);
lean_inc_ref(v_attr_512_);
lean_dec_ref(v_attr_433_);
v_toAttributeImplCore_513_ = lean_ctor_get(v_attr_512_, 0);
lean_inc_ref(v_toAttributeImplCore_513_);
lean_dec_ref(v_attr_512_);
v_name_514_ = lean_ctor_get(v_toAttributeImplCore_513_, 1);
lean_inc(v_name_514_);
lean_dec_ref(v_toAttributeImplCore_513_);
v___x_515_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_name_514_, v_decl_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
return v___x_515_;
}
v___jp_440_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v_mctx_456_; lean_object* v_zetaDeltaFVarIds_457_; lean_object* v_postponed_458_; lean_object* v_diag_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_470_; 
v___x_452_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_453_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_453_, 0, v___y_451_);
lean_ctor_set(v___x_453_, 1, v___y_444_);
lean_ctor_set(v___x_453_, 2, v___y_442_);
lean_ctor_set(v___x_453_, 3, v___y_445_);
lean_ctor_set(v___x_453_, 4, v___y_443_);
lean_ctor_set(v___x_453_, 5, v___x_452_);
lean_ctor_set(v___x_453_, 6, v___y_441_);
lean_ctor_set(v___x_453_, 7, v___y_448_);
lean_ctor_set(v___x_453_, 8, v___y_447_);
lean_ctor_set(v___x_453_, 9, v___y_450_);
v___x_454_ = lean_st_ref_put(v___y_449_, v___x_453_);
v___x_455_ = lean_st_ref_take(v___y_446_);
v_mctx_456_ = lean_ctor_get(v___x_455_, 0);
v_zetaDeltaFVarIds_457_ = lean_ctor_get(v___x_455_, 2);
v_postponed_458_ = lean_ctor_get(v___x_455_, 3);
v_diag_459_ = lean_ctor_get(v___x_455_, 4);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v___x_455_, 1);
lean_dec(v_unused_471_);
v___x_461_ = v___x_455_;
v_isShared_462_ = v_isSharedCheck_470_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_diag_459_);
lean_inc(v_postponed_458_);
lean_inc(v_zetaDeltaFVarIds_457_);
lean_inc(v_mctx_456_);
lean_dec(v___x_455_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_470_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = lean_box(0);
v___x_464_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_464_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_mctx_456_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_zetaDeltaFVarIds_457_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_postponed_458_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_diag_459_);
v___x_466_ = v_reuseFailAlloc_469_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_st_ref_put(v___y_446_, v___x_466_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_463_);
return v___x_468_;
}
}
}
v___jp_472_:
{
lean_object* v___x_475_; lean_object* v_ext_476_; lean_object* v_toEnvExtension_477_; lean_object* v_env_478_; lean_object* v_nextMacroScope_479_; lean_object* v_ngen_480_; lean_object* v_auxDeclNGen_481_; lean_object* v_traceState_482_; lean_object* v_recordedDeps_483_; lean_object* v_messages_484_; lean_object* v_infoState_485_; lean_object* v_snapshotTasks_486_; lean_object* v_addEntryFn_487_; lean_object* v_asyncMode_488_; uint8_t v_logWrites_489_; lean_object* v___f_490_; uint8_t v___x_491_; 
v___x_475_ = lean_st_ref_take(v___y_474_);
v_ext_476_ = lean_ctor_get(v_attr_433_, 1);
lean_inc_ref(v_ext_476_);
lean_dec_ref(v_attr_433_);
v_toEnvExtension_477_ = lean_ctor_get(v_ext_476_, 0);
lean_inc_ref(v_toEnvExtension_477_);
v_env_478_ = lean_ctor_get(v___x_475_, 0);
lean_inc_ref(v_env_478_);
v_nextMacroScope_479_ = lean_ctor_get(v___x_475_, 1);
lean_inc(v_nextMacroScope_479_);
v_ngen_480_ = lean_ctor_get(v___x_475_, 2);
lean_inc_ref(v_ngen_480_);
v_auxDeclNGen_481_ = lean_ctor_get(v___x_475_, 3);
lean_inc_ref(v_auxDeclNGen_481_);
v_traceState_482_ = lean_ctor_get(v___x_475_, 4);
lean_inc_ref(v_traceState_482_);
v_recordedDeps_483_ = lean_ctor_get(v___x_475_, 6);
lean_inc_ref(v_recordedDeps_483_);
v_messages_484_ = lean_ctor_get(v___x_475_, 7);
lean_inc_ref(v_messages_484_);
v_infoState_485_ = lean_ctor_get(v___x_475_, 8);
lean_inc_ref(v_infoState_485_);
v_snapshotTasks_486_ = lean_ctor_get(v___x_475_, 9);
lean_inc_ref(v_snapshotTasks_486_);
lean_dec(v___x_475_);
v_addEntryFn_487_ = lean_ctor_get(v_ext_476_, 3);
lean_inc(v_addEntryFn_487_);
lean_dec_ref(v_ext_476_);
v_asyncMode_488_ = lean_ctor_get(v_toEnvExtension_477_, 2);
lean_inc(v_asyncMode_488_);
v_logWrites_489_ = lean_ctor_get_uint8(v_toEnvExtension_477_, sizeof(void*)*6);
lean_inc(v_decl_434_);
v___f_490_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_490_, 0, v_addEntryFn_487_);
lean_closure_set(v___f_490_, 1, v_decl_434_);
v___x_491_ = 1;
if (v_logWrites_489_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_477_, v_env_478_, v___f_490_, v_asyncMode_488_, v_decl_434_, v___x_491_);
lean_dec(v_asyncMode_488_);
v___y_441_ = v_recordedDeps_483_;
v___y_442_ = v_ngen_480_;
v___y_443_ = v_traceState_482_;
v___y_444_ = v_nextMacroScope_479_;
v___y_445_ = v_auxDeclNGen_481_;
v___y_446_ = v___y_473_;
v___y_447_ = v_infoState_485_;
v___y_448_ = v_messages_484_;
v___y_449_ = v___y_474_;
v___y_450_ = v_snapshotTasks_486_;
v___y_451_ = v___x_492_;
goto v___jp_440_;
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_inc_ref(v_toEnvExtension_477_);
v___x_493_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_477_, v_env_478_);
lean_dec_ref(v_env_478_);
v___x_494_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_477_, v___x_493_, v___f_490_, v_asyncMode_488_, v_decl_434_, v___x_491_);
lean_dec(v_asyncMode_488_);
v___y_441_ = v_recordedDeps_483_;
v___y_442_ = v_ngen_480_;
v___y_443_ = v_traceState_482_;
v___y_444_ = v_nextMacroScope_479_;
v___y_445_ = v_auxDeclNGen_481_;
v___y_446_ = v___y_473_;
v___y_447_ = v_infoState_485_;
v___y_448_ = v_messages_484_;
v___y_449_ = v___y_474_;
v___y_450_ = v_snapshotTasks_486_;
v___y_451_ = v___x_494_;
goto v___jp_440_;
}
}
v___jp_497_:
{
lean_object* v_ext_502_; lean_object* v_toEnvExtension_503_; lean_object* v_attr_504_; lean_object* v_asyncMode_505_; uint8_t v___x_506_; 
v_ext_502_ = lean_ctor_get(v_attr_433_, 1);
v_toEnvExtension_503_ = lean_ctor_get(v_ext_502_, 0);
v_attr_504_ = lean_ctor_get(v_attr_433_, 0);
v_asyncMode_505_ = lean_ctor_get(v_toEnvExtension_503_, 2);
lean_inc(v_decl_434_);
lean_inc_ref(v_env_496_);
v___x_506_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_496_, v_decl_434_, v_asyncMode_505_);
if (v___x_506_ == 0)
{
lean_object* v_toAttributeImplCore_507_; lean_object* v_name_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_inc_ref(v_attr_504_);
lean_dec_ref(v_attr_433_);
v_toAttributeImplCore_507_ = lean_ctor_get(v_attr_504_, 0);
lean_inc_ref(v_toAttributeImplCore_507_);
lean_dec_ref(v_attr_504_);
v_name_508_ = lean_ctor_get(v_toAttributeImplCore_507_, 1);
lean_inc(v_name_508_);
lean_dec_ref(v_toAttributeImplCore_507_);
v___x_509_ = l_Lean_Environment_asyncPrefix_x3f(v_env_496_);
v___x_510_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_name_508_, v_decl_434_, v___x_509_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
return v___x_510_;
}
else
{
lean_dec_ref(v_env_496_);
v___y_473_ = v___y_499_;
v___y_474_ = v___y_501_;
goto v___jp_472_;
}
}
}
}
LEAN_EXPORT void l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_attr_433_ = stack[0].m_obj;
lean_object* v_decl_434_ = stack[1].m_obj;
lean_object* v___y_435_ = stack[2].m_obj;
lean_object* v___y_436_ = stack[3].m_obj;
lean_object* v___y_437_ = stack[4].m_obj;
lean_object* v___y_438_ = stack[5].m_obj;
lean_object* v_res_516_;
v_res_516_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v_attr_433_, v_decl_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object* v_attr_517_, lean_object* v_decl_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v_attr_517_, v_decl_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(lean_object* v_keys_525_, lean_object* v_vals_526_, lean_object* v_i_527_, lean_object* v_k_528_){
_start:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_array_get_size(v_keys_525_);
v___x_530_ = lean_nat_dec_lt(v_i_527_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
lean_dec(v_i_527_);
v___x_531_ = lean_box(0);
return v___x_531_;
}
else
{
lean_object* v_k_x27_532_; uint8_t v___x_533_; 
v_k_x27_532_ = lean_array_fget_borrowed(v_keys_525_, v_i_527_);
v___x_533_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_k_528_, v_k_x27_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_i_527_, v___x_534_);
lean_dec(v_i_527_);
v_i_527_ = v___x_535_;
goto _start;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_array_fget_borrowed(v_vals_526_, v_i_527_);
lean_dec(v_i_527_);
lean_inc(v___x_537_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_keys_539_, lean_object* v_vals_540_, lean_object* v_i_541_, lean_object* v_k_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_539_, v_vals_540_, v_i_541_, v_k_542_);
lean_dec_ref(v_k_542_);
lean_dec_ref(v_vals_540_);
lean_dec_ref(v_keys_539_);
return v_res_543_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(lean_object* v_x_544_, size_t v_x_545_, lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_es_547_; lean_object* v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v_j_551_; lean_object* v___x_552_; 
v_es_547_ = lean_ctor_get(v_x_544_, 0);
v___x_548_ = lean_box(2);
v___x_549_ = ((size_t)31ULL);
v___x_550_ = lean_usize_land(v_x_545_, v___x_549_);
v_j_551_ = lean_usize_to_nat(v___x_550_);
v___x_552_ = lean_array_get_borrowed(v___x_548_, v_es_547_, v_j_551_);
lean_dec(v_j_551_);
switch(lean_obj_tag(v___x_552_))
{
case 0:
{
lean_object* v_key_553_; lean_object* v_val_554_; uint8_t v___x_555_; 
v_key_553_ = lean_ctor_get(v___x_552_, 0);
v_val_554_ = lean_ctor_get(v___x_552_, 1);
v___x_555_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_546_, v_key_553_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_box(0);
return v___x_556_;
}
else
{
lean_object* v___x_557_; 
lean_inc(v_val_554_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_val_554_);
return v___x_557_;
}
}
case 1:
{
lean_object* v_node_558_; size_t v___x_559_; size_t v___x_560_; 
v_node_558_ = lean_ctor_get(v___x_552_, 0);
v___x_559_ = ((size_t)5ULL);
v___x_560_ = lean_usize_shift_right(v_x_545_, v___x_559_);
v_x_544_ = v_node_558_;
v_x_545_ = v___x_560_;
goto _start;
}
default: 
{
lean_object* v___x_562_; 
v___x_562_ = lean_box(0);
return v___x_562_;
}
}
}
else
{
lean_object* v_ks_563_; lean_object* v_vs_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_ks_563_ = lean_ctor_get(v_x_544_, 0);
v_vs_564_ = lean_ctor_get(v_x_544_, 1);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_ks_563_, v_vs_564_, v___x_565_, v_x_546_);
return v___x_566_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_544_ = stack[0].m_obj;
size_t v_x_545_ = stack[1].m_num;
lean_object* v_x_546_ = stack[2].m_obj;
lean_object* v_res_567_;
v_res_567_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_544_, v_x_545_, v_x_546_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg___boxed(lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
size_t v_x_6500__boxed_571_; lean_object* v_res_572_; 
v_x_6500__boxed_571_ = lean_unbox_usize(v_x_569_);
lean_dec(v_x_569_);
v_res_572_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_568_, v_x_6500__boxed_571_, v_x_570_);
lean_dec_ref(v_x_570_);
lean_dec_ref(v_x_568_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
uint64_t v___x_575_; size_t v___x_576_; lean_object* v___x_577_; 
v___x_575_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_574_);
v___x_576_ = lean_uint64_to_usize(v___x_575_);
v___x_577_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_573_, v___x_576_, v_x_574_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg___boxed(lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_578_, v_x_579_);
lean_dec_ref(v_x_579_);
lean_dec_ref(v_x_578_);
return v_res_580_;
}
}
uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
if (lean_obj_tag(v_x_582_) == 0)
{
uint8_t v___x_583_; 
v___x_583_ = 1;
return v___x_583_;
}
else
{
uint8_t v___x_584_; 
v___x_584_ = 0;
return v___x_584_;
}
}
else
{
if (lean_obj_tag(v_x_582_) == 0)
{
uint8_t v___x_585_; 
v___x_585_ = 0;
return v___x_585_;
}
else
{
lean_object* v_head_586_; lean_object* v_tail_587_; lean_object* v_head_588_; lean_object* v_tail_589_; uint8_t v___x_590_; 
v_head_586_ = lean_ctor_get(v_x_581_, 0);
v_tail_587_ = lean_ctor_get(v_x_581_, 1);
v_head_588_ = lean_ctor_get(v_x_582_, 0);
v_tail_589_ = lean_ctor_get(v_x_582_, 1);
v___x_590_ = lean_name_eq(v_head_586_, v_head_588_);
if (v___x_590_ == 0)
{
return v___x_590_;
}
else
{
v_x_581_ = v_tail_587_;
v_x_582_ = v_tail_589_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_581_ = stack[0].m_obj;
lean_object* v_x_582_ = stack[1].m_obj;
uint8_t v_res_592_;
v_res_592_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_x_581_, v_x_582_);
stack->m_num = v_res_592_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4___boxed(lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_x_593_, v_x_594_);
lean_dec(v_x_594_);
lean_dec(v_x_593_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
lean_object* l_Lean_Meta_mkAuxLemma(lean_object* v_levelParams_600_, lean_object* v_type_601_, lean_object* v_value_602_, lean_object* v_kind_x3f_603_, uint8_t v_cache_604_, uint8_t v_inferRfl_605_, uint8_t v_forceExpose_606_, uint8_t v_defeq_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v_nextMacroScope_616_; lean_object* v_ngen_617_; lean_object* v_auxDeclNGen_618_; lean_object* v_traceState_619_; lean_object* v_recordedDeps_620_; lean_object* v_messages_621_; lean_object* v_infoState_622_; lean_object* v_snapshotTasks_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v_nextMacroScope_649_; lean_object* v_ngen_650_; lean_object* v_auxDeclNGen_651_; lean_object* v_traceState_652_; lean_object* v_recordedDeps_653_; lean_object* v_messages_654_; lean_object* v_infoState_655_; lean_object* v_snapshotTasks_656_; lean_object* v___y_657_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_env_679_; lean_object* v___x_680_; lean_object* v_asyncMode_681_; uint8_t v_logWrites_682_; uint8_t v_isExporting_683_; lean_object* v___x_684_; lean_object* v___y_686_; lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_714_; lean_object* v___y_715_; uint8_t v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; uint8_t v___y_737_; lean_object* v___y_738_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v___y_765_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; uint8_t v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; uint8_t v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; uint8_t v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_861_; lean_object* v___y_862_; uint8_t v___y_863_; uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___y_880_; uint8_t v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; uint8_t v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; uint8_t v___y_922_; 
v___x_677_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_678_ = lean_st_ref_get(v_a_611_);
v_env_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc_ref_n(v_env_679_, 2);
lean_dec(v___x_678_);
v___x_680_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_681_ = lean_ctor_get(v___x_680_, 2);
v_logWrites_682_ = lean_ctor_get_uint8(v___x_680_, sizeof(void*)*6);
v_isExporting_683_ = lean_ctor_get_uint8(v_env_679_, sizeof(void*)*13);
v___x_684_ = lean_box(0);
v___x_877_ = 0;
v___x_878_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_677_, v___x_680_, v_env_679_, v_asyncMode_681_, v___x_684_, v___x_877_);
if (v_isExporting_683_ == 0)
{
uint8_t v___x_926_; 
v___x_926_ = 1;
v___y_922_ = v___x_926_;
goto v___jp_921_;
}
else
{
v___y_922_ = v___x_877_;
goto v___jp_921_;
}
v___jp_613_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v_mctx_630_; lean_object* v_zetaDeltaFVarIds_631_; lean_object* v_postponed_632_; lean_object* v_diag_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_643_; 
v___x_626_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_627_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_627_, 0, v___y_625_);
lean_ctor_set(v___x_627_, 1, v_nextMacroScope_616_);
lean_ctor_set(v___x_627_, 2, v_ngen_617_);
lean_ctor_set(v___x_627_, 3, v_auxDeclNGen_618_);
lean_ctor_set(v___x_627_, 4, v_traceState_619_);
lean_ctor_set(v___x_627_, 5, v___x_626_);
lean_ctor_set(v___x_627_, 6, v_recordedDeps_620_);
lean_ctor_set(v___x_627_, 7, v_messages_621_);
lean_ctor_set(v___x_627_, 8, v_infoState_622_);
lean_ctor_set(v___x_627_, 9, v_snapshotTasks_623_);
v___x_628_ = lean_st_ref_put(v___y_614_, v___x_627_);
v___x_629_ = lean_st_ref_take(v___y_615_);
v_mctx_630_ = lean_ctor_get(v___x_629_, 0);
v_zetaDeltaFVarIds_631_ = lean_ctor_get(v___x_629_, 2);
v_postponed_632_ = lean_ctor_get(v___x_629_, 3);
v_diag_633_ = lean_ctor_get(v___x_629_, 4);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v___x_629_, 1);
lean_dec(v_unused_644_);
v___x_635_ = v___x_629_;
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_diag_633_);
lean_inc(v_postponed_632_);
lean_inc(v_zetaDeltaFVarIds_631_);
lean_inc(v_mctx_630_);
lean_dec(v___x_629_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v___x_637_);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_mctx_630_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_zetaDeltaFVarIds_631_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v_postponed_632_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v_diag_633_);
v___x_639_ = v_reuseFailAlloc_642_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_st_ref_put(v___y_615_, v___x_639_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___y_624_);
return v___x_641_;
}
}
}
v___jp_645_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_mctx_662_; lean_object* v_zetaDeltaFVarIds_663_; lean_object* v_postponed_664_; lean_object* v_diag_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_675_; 
v___x_658_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__1);
v___x_659_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_659_, 0, v___y_657_);
lean_ctor_set(v___x_659_, 1, v_nextMacroScope_649_);
lean_ctor_set(v___x_659_, 2, v_ngen_650_);
lean_ctor_set(v___x_659_, 3, v_auxDeclNGen_651_);
lean_ctor_set(v___x_659_, 4, v_traceState_652_);
lean_ctor_set(v___x_659_, 5, v___x_658_);
lean_ctor_set(v___x_659_, 6, v_recordedDeps_653_);
lean_ctor_set(v___x_659_, 7, v_messages_654_);
lean_ctor_set(v___x_659_, 8, v_infoState_655_);
lean_ctor_set(v___x_659_, 9, v_snapshotTasks_656_);
v___x_660_ = lean_st_ref_put(v___y_648_, v___x_659_);
v___x_661_ = lean_st_ref_take(v___y_647_);
v_mctx_662_ = lean_ctor_get(v___x_661_, 0);
v_zetaDeltaFVarIds_663_ = lean_ctor_get(v___x_661_, 2);
v_postponed_664_ = lean_ctor_get(v___x_661_, 3);
v_diag_665_ = lean_ctor_get(v___x_661_, 4);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v___x_661_, 1);
lean_dec(v_unused_676_);
v___x_667_ = v___x_661_;
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_diag_665_);
lean_inc(v_postponed_664_);
lean_inc(v_zetaDeltaFVarIds_663_);
lean_inc(v_mctx_662_);
lean_dec(v___x_661_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_obj_once(&l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2, &l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2_once, _init_l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2___closed__2);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_mctx_662_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_zetaDeltaFVarIds_663_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_postponed_664_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_diag_665_);
v___x_671_ = v_reuseFailAlloc_674_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_st_ref_put(v___y_647_, v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___y_646_);
return v___x_673_;
}
}
}
v___jp_685_:
{
lean_object* v___x_691_; 
v___x_691_ = lean_st_ref_take(v___y_690_);
if (v_logWrites_682_ == 0)
{
lean_object* v_env_692_; lean_object* v_nextMacroScope_693_; lean_object* v_ngen_694_; lean_object* v_auxDeclNGen_695_; lean_object* v_traceState_696_; lean_object* v_recordedDeps_697_; lean_object* v_messages_698_; lean_object* v_infoState_699_; lean_object* v_snapshotTasks_700_; lean_object* v___x_701_; 
v_env_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref(v_env_692_);
v_nextMacroScope_693_ = lean_ctor_get(v___x_691_, 1);
lean_inc(v_nextMacroScope_693_);
v_ngen_694_ = lean_ctor_get(v___x_691_, 2);
lean_inc_ref(v_ngen_694_);
v_auxDeclNGen_695_ = lean_ctor_get(v___x_691_, 3);
lean_inc_ref(v_auxDeclNGen_695_);
v_traceState_696_ = lean_ctor_get(v___x_691_, 4);
lean_inc_ref(v_traceState_696_);
v_recordedDeps_697_ = lean_ctor_get(v___x_691_, 6);
lean_inc_ref(v_recordedDeps_697_);
v_messages_698_ = lean_ctor_get(v___x_691_, 7);
lean_inc_ref(v_messages_698_);
v_infoState_699_ = lean_ctor_get(v___x_691_, 8);
lean_inc_ref(v_infoState_699_);
v_snapshotTasks_700_ = lean_ctor_get(v___x_691_, 9);
lean_inc_ref(v_snapshotTasks_700_);
lean_dec(v___x_691_);
v___x_701_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_680_, v_env_692_, v___y_687_, v_asyncMode_681_, v___x_684_, v___y_688_);
v___y_646_ = v___y_686_;
v___y_647_ = v___y_689_;
v___y_648_ = v___y_690_;
v_nextMacroScope_649_ = v_nextMacroScope_693_;
v_ngen_650_ = v_ngen_694_;
v_auxDeclNGen_651_ = v_auxDeclNGen_695_;
v_traceState_652_ = v_traceState_696_;
v_recordedDeps_653_ = v_recordedDeps_697_;
v_messages_654_ = v_messages_698_;
v_infoState_655_ = v_infoState_699_;
v_snapshotTasks_656_ = v_snapshotTasks_700_;
v___y_657_ = v___x_701_;
goto v___jp_645_;
}
else
{
lean_object* v_env_702_; lean_object* v_nextMacroScope_703_; lean_object* v_ngen_704_; lean_object* v_auxDeclNGen_705_; lean_object* v_traceState_706_; lean_object* v_recordedDeps_707_; lean_object* v_messages_708_; lean_object* v_infoState_709_; lean_object* v_snapshotTasks_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_env_702_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref(v_env_702_);
v_nextMacroScope_703_ = lean_ctor_get(v___x_691_, 1);
lean_inc(v_nextMacroScope_703_);
v_ngen_704_ = lean_ctor_get(v___x_691_, 2);
lean_inc_ref(v_ngen_704_);
v_auxDeclNGen_705_ = lean_ctor_get(v___x_691_, 3);
lean_inc_ref(v_auxDeclNGen_705_);
v_traceState_706_ = lean_ctor_get(v___x_691_, 4);
lean_inc_ref(v_traceState_706_);
v_recordedDeps_707_ = lean_ctor_get(v___x_691_, 6);
lean_inc_ref(v_recordedDeps_707_);
v_messages_708_ = lean_ctor_get(v___x_691_, 7);
lean_inc_ref(v_messages_708_);
v_infoState_709_ = lean_ctor_get(v___x_691_, 8);
lean_inc_ref(v_infoState_709_);
v_snapshotTasks_710_ = lean_ctor_get(v___x_691_, 9);
lean_inc_ref(v_snapshotTasks_710_);
lean_dec(v___x_691_);
v___x_711_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_680_, v_env_702_);
lean_dec_ref(v_env_702_);
v___x_712_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_680_, v___x_711_, v___y_687_, v_asyncMode_681_, v___x_684_, v___y_688_);
v___y_646_ = v___y_686_;
v___y_647_ = v___y_689_;
v___y_648_ = v___y_690_;
v_nextMacroScope_649_ = v_nextMacroScope_703_;
v_ngen_650_ = v_ngen_704_;
v_auxDeclNGen_651_ = v_auxDeclNGen_705_;
v_traceState_652_ = v_traceState_706_;
v_recordedDeps_653_ = v_recordedDeps_707_;
v_messages_654_ = v_messages_708_;
v_infoState_655_ = v_infoState_709_;
v_snapshotTasks_656_ = v_snapshotTasks_710_;
v___y_657_ = v___x_712_;
goto v___jp_645_;
}
}
v___jp_713_:
{
if (v_inferRfl_605_ == 0)
{
v___y_686_ = v___y_714_;
v___y_687_ = v___y_715_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_718_;
v___y_690_ = v___y_720_;
goto v___jp_685_;
}
else
{
lean_object* v___x_721_; 
lean_inc(v___y_714_);
v___x_721_ = l_Lean_inferDefEqAttr(v___y_714_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_dec_ref_known(v___x_721_, 1);
v___y_686_ = v___y_714_;
v___y_687_ = v___y_715_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_718_;
v___y_690_ = v___y_720_;
goto v___jp_685_;
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
v___jp_730_:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_addDecl(v___y_738_, v_forceExpose_606_, v___y_734_, v___y_732_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_dec_ref_known(v___x_739_, 1);
if (v_defeq_607_ == 0)
{
v___y_714_ = v___y_731_;
v___y_715_ = v___y_735_;
v___y_716_ = v___y_737_;
v___y_717_ = v___y_736_;
v___y_718_ = v___y_733_;
v___y_719_ = v___y_734_;
v___y_720_ = v___y_732_;
goto v___jp_713_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = l_Lean_defeqAttr;
lean_inc(v___y_731_);
v___x_741_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_740_, v___y_731_, v___y_736_, v___y_733_, v___y_734_, v___y_732_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_dec_ref_known(v___x_741_, 1);
v___y_714_ = v___y_731_;
v___y_715_ = v___y_735_;
v___y_716_ = v___y_737_;
v___y_717_ = v___y_736_;
v___y_718_ = v___y_733_;
v___y_719_ = v___y_734_;
v___y_720_ = v___y_732_;
goto v___jp_713_;
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v___y_735_);
lean_dec(v___y_731_);
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
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
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v___y_735_);
lean_dec(v___y_731_);
v_a_750_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_739_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_739_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
v___jp_758_:
{
uint8_t v___x_766_; 
v___x_766_ = 1;
if (v___y_765_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_inc_n(v___y_759_, 2);
v___x_767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_767_, 0, v___y_759_);
lean_ctor_set(v___x_767_, 1, v_levelParams_600_);
lean_ctor_set(v___x_767_, 2, v_type_601_);
v___x_768_ = lean_box(0);
v___x_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_769_, 0, v___y_759_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_770_, 0, v___x_767_);
lean_ctor_set(v___x_770_, 1, v_value_602_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
v___x_771_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
v___y_731_ = v___y_759_;
v___y_732_ = v___y_760_;
v___y_733_ = v___y_761_;
v___y_734_ = v___y_762_;
v___y_735_ = v___y_763_;
v___y_736_ = v___y_764_;
v___y_737_ = v___x_766_;
v___y_738_ = v___x_771_;
goto v___jp_730_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_inc_n(v___y_759_, 2);
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v___y_759_);
lean_ctor_set(v___x_772_, 1, v_levelParams_600_);
lean_ctor_set(v___x_772_, 2, v_type_601_);
v___x_773_ = lean_box(0);
v___x_774_ = 0;
v___x_775_ = lean_box(0);
v___x_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_776_, 0, v___y_759_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_777_, 0, v___x_772_);
lean_ctor_set(v___x_777_, 1, v_value_602_);
lean_ctor_set(v___x_777_, 2, v___x_773_);
lean_ctor_set(v___x_777_, 3, v___x_776_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*4, v___x_774_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
v___y_731_ = v___y_759_;
v___y_732_ = v___y_760_;
v___y_733_ = v___y_761_;
v___y_734_ = v___y_762_;
v___y_735_ = v___y_763_;
v___y_736_ = v___y_764_;
v___y_737_ = v___x_766_;
v___y_738_ = v___x_778_;
goto v___jp_730_;
}
}
v___jp_779_:
{
lean_object* v___x_786_; lean_object* v_a_787_; lean_object* v___f_788_; uint8_t v___x_789_; 
v___x_786_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_781_, v___y_785_);
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc_n(v_a_787_, 2);
lean_dec_ref(v___x_786_);
lean_inc(v_levelParams_600_);
v___f_788_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_788_, 0, v_a_787_);
lean_closure_set(v___f_788_, 1, v_levelParams_600_);
lean_closure_set(v___f_788_, 2, v___y_780_);
lean_inc_ref(v_env_679_);
v___x_789_ = l_Lean_Environment_hasUnsafe(v_env_679_, v_type_601_);
if (v___x_789_ == 0)
{
uint8_t v___x_790_; 
v___x_790_ = l_Lean_Environment_hasUnsafe(v_env_679_, v_value_602_);
v___y_759_ = v_a_787_;
v___y_760_ = v___y_785_;
v___y_761_ = v___y_783_;
v___y_762_ = v___y_784_;
v___y_763_ = v___f_788_;
v___y_764_ = v___y_782_;
v___y_765_ = v___x_790_;
goto v___jp_758_;
}
else
{
lean_dec_ref(v_env_679_);
v___y_759_ = v_a_787_;
v___y_760_ = v___y_785_;
v___y_761_ = v___y_783_;
v___y_762_ = v___y_784_;
v___y_763_ = v___f_788_;
v___y_764_ = v___y_782_;
v___y_765_ = v___x_789_;
goto v___jp_758_;
}
}
v___jp_791_:
{
lean_object* v___x_797_; 
v___x_797_ = lean_st_ref_take(v___y_796_);
if (v_logWrites_682_ == 0)
{
lean_object* v_env_798_; lean_object* v_nextMacroScope_799_; lean_object* v_ngen_800_; lean_object* v_auxDeclNGen_801_; lean_object* v_traceState_802_; lean_object* v_recordedDeps_803_; lean_object* v_messages_804_; lean_object* v_infoState_805_; lean_object* v_snapshotTasks_806_; lean_object* v___x_807_; 
v_env_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc_ref(v_env_798_);
v_nextMacroScope_799_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_nextMacroScope_799_);
v_ngen_800_ = lean_ctor_get(v___x_797_, 2);
lean_inc_ref(v_ngen_800_);
v_auxDeclNGen_801_ = lean_ctor_get(v___x_797_, 3);
lean_inc_ref(v_auxDeclNGen_801_);
v_traceState_802_ = lean_ctor_get(v___x_797_, 4);
lean_inc_ref(v_traceState_802_);
v_recordedDeps_803_ = lean_ctor_get(v___x_797_, 6);
lean_inc_ref(v_recordedDeps_803_);
v_messages_804_ = lean_ctor_get(v___x_797_, 7);
lean_inc_ref(v_messages_804_);
v_infoState_805_ = lean_ctor_get(v___x_797_, 8);
lean_inc_ref(v_infoState_805_);
v_snapshotTasks_806_ = lean_ctor_get(v___x_797_, 9);
lean_inc_ref(v_snapshotTasks_806_);
lean_dec(v___x_797_);
v___x_807_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_680_, v_env_798_, v___y_793_, v_asyncMode_681_, v___x_684_, v___y_792_);
v___y_614_ = v___y_796_;
v___y_615_ = v___y_795_;
v_nextMacroScope_616_ = v_nextMacroScope_799_;
v_ngen_617_ = v_ngen_800_;
v_auxDeclNGen_618_ = v_auxDeclNGen_801_;
v_traceState_619_ = v_traceState_802_;
v_recordedDeps_620_ = v_recordedDeps_803_;
v_messages_621_ = v_messages_804_;
v_infoState_622_ = v_infoState_805_;
v_snapshotTasks_623_ = v_snapshotTasks_806_;
v___y_624_ = v___y_794_;
v___y_625_ = v___x_807_;
goto v___jp_613_;
}
else
{
lean_object* v_env_808_; lean_object* v_nextMacroScope_809_; lean_object* v_ngen_810_; lean_object* v_auxDeclNGen_811_; lean_object* v_traceState_812_; lean_object* v_recordedDeps_813_; lean_object* v_messages_814_; lean_object* v_infoState_815_; lean_object* v_snapshotTasks_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_env_808_ = lean_ctor_get(v___x_797_, 0);
lean_inc_ref(v_env_808_);
v_nextMacroScope_809_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_nextMacroScope_809_);
v_ngen_810_ = lean_ctor_get(v___x_797_, 2);
lean_inc_ref(v_ngen_810_);
v_auxDeclNGen_811_ = lean_ctor_get(v___x_797_, 3);
lean_inc_ref(v_auxDeclNGen_811_);
v_traceState_812_ = lean_ctor_get(v___x_797_, 4);
lean_inc_ref(v_traceState_812_);
v_recordedDeps_813_ = lean_ctor_get(v___x_797_, 6);
lean_inc_ref(v_recordedDeps_813_);
v_messages_814_ = lean_ctor_get(v___x_797_, 7);
lean_inc_ref(v_messages_814_);
v_infoState_815_ = lean_ctor_get(v___x_797_, 8);
lean_inc_ref(v_infoState_815_);
v_snapshotTasks_816_ = lean_ctor_get(v___x_797_, 9);
lean_inc_ref(v_snapshotTasks_816_);
lean_dec(v___x_797_);
v___x_817_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_680_, v_env_808_);
lean_dec_ref(v_env_808_);
v___x_818_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_680_, v___x_817_, v___y_793_, v_asyncMode_681_, v___x_684_, v___y_792_);
v___y_614_ = v___y_796_;
v___y_615_ = v___y_795_;
v_nextMacroScope_616_ = v_nextMacroScope_809_;
v_ngen_617_ = v_ngen_810_;
v_auxDeclNGen_618_ = v_auxDeclNGen_811_;
v_traceState_619_ = v_traceState_812_;
v_recordedDeps_620_ = v_recordedDeps_813_;
v_messages_621_ = v_messages_814_;
v_infoState_622_ = v_infoState_815_;
v_snapshotTasks_623_ = v_snapshotTasks_816_;
v___y_624_ = v___y_794_;
v___y_625_ = v___x_818_;
goto v___jp_613_;
}
}
v___jp_819_:
{
if (v_inferRfl_605_ == 0)
{
v___y_792_ = v___y_820_;
v___y_793_ = v___y_821_;
v___y_794_ = v___y_822_;
v___y_795_ = v___y_824_;
v___y_796_ = v___y_826_;
goto v___jp_791_;
}
else
{
lean_object* v___x_827_; 
lean_inc(v___y_822_);
v___x_827_ = l_Lean_inferDefEqAttr(v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_dec_ref_known(v___x_827_, 1);
v___y_792_ = v___y_820_;
v___y_793_ = v___y_821_;
v___y_794_ = v___y_822_;
v___y_795_ = v___y_824_;
v___y_796_ = v___y_826_;
goto v___jp_791_;
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
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
}
v___jp_836_:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_addDecl(v___y_840_, v_forceExpose_606_, v_a_610_, v_a_611_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_dec_ref_known(v___x_841_, 1);
if (v_defeq_607_ == 0)
{
v___y_820_ = v___y_837_;
v___y_821_ = v___y_838_;
v___y_822_ = v___y_839_;
v___y_823_ = v_a_608_;
v___y_824_ = v_a_609_;
v___y_825_ = v_a_610_;
v___y_826_ = v_a_611_;
goto v___jp_819_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = l_Lean_defeqAttr;
lean_inc(v___y_839_);
v___x_843_ = l_Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2(v___x_842_, v___y_839_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_dec_ref_known(v___x_843_, 1);
v___y_820_ = v___y_837_;
v___y_821_ = v___y_838_;
v___y_822_ = v___y_839_;
v___y_823_ = v_a_608_;
v___y_824_ = v_a_609_;
v___y_825_ = v_a_610_;
v___y_826_ = v_a_611_;
goto v___jp_819_;
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
v_a_852_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_841_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_841_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
v___jp_860_:
{
uint8_t v___x_864_; 
v___x_864_ = 1;
if (v___y_863_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
lean_inc_n(v___y_862_, 2);
v___x_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_865_, 0, v___y_862_);
lean_ctor_set(v___x_865_, 1, v_levelParams_600_);
lean_ctor_set(v___x_865_, 2, v_type_601_);
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v___y_862_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_868_, 0, v___x_865_);
lean_ctor_set(v___x_868_, 1, v_value_602_);
lean_ctor_set(v___x_868_, 2, v___x_867_);
v___x_869_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
v___y_837_ = v___x_864_;
v___y_838_ = v___y_861_;
v___y_839_ = v___y_862_;
v___y_840_ = v___x_869_;
goto v___jp_836_;
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_inc_n(v___y_862_, 2);
v___x_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_870_, 0, v___y_862_);
lean_ctor_set(v___x_870_, 1, v_levelParams_600_);
lean_ctor_set(v___x_870_, 2, v_type_601_);
v___x_871_ = lean_box(0);
v___x_872_ = 0;
v___x_873_ = lean_box(0);
v___x_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_874_, 0, v___y_862_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_875_, 0, v___x_870_);
lean_ctor_set(v___x_875_, 1, v_value_602_);
lean_ctor_set(v___x_875_, 2, v___x_871_);
lean_ctor_set(v___x_875_, 3, v___x_874_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*4, v___x_872_);
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
v___y_837_ = v___x_864_;
v___y_838_ = v___y_861_;
v___y_839_ = v___y_862_;
v___y_840_ = v___x_876_;
goto v___jp_836_;
}
}
v___jp_879_:
{
if (v___y_881_ == 0)
{
lean_dec(v___x_878_);
v___y_780_ = v___y_880_;
v___y_781_ = v___y_882_;
v___y_782_ = v___y_883_;
v___y_783_ = v___y_884_;
v___y_784_ = v___y_885_;
v___y_785_ = v___y_886_;
goto v___jp_779_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_inc_ref(v_type_601_);
v___x_887_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_887_, 0, v_type_601_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*1, v___x_877_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*1 + 1, v_defeq_607_);
v___x_888_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_878_, v___x_887_);
lean_dec_ref_known(v___x_887_, 1);
lean_dec(v___x_878_);
if (lean_obj_tag(v___x_888_) == 1)
{
lean_object* v_val_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_899_; 
v_val_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_899_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_val_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_fst_893_; lean_object* v_snd_894_; uint8_t v___x_895_; 
v_fst_893_ = lean_ctor_get(v_val_889_, 0);
lean_inc(v_fst_893_);
v_snd_894_ = lean_ctor_get(v_val_889_, 1);
lean_inc(v_snd_894_);
lean_dec(v_val_889_);
v___x_895_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_600_, v_snd_894_);
lean_dec(v_snd_894_);
if (v___x_895_ == 0)
{
lean_dec(v_fst_893_);
lean_del_object(v___x_891_);
v___y_780_ = v___y_880_;
v___y_781_ = v___y_882_;
v___y_782_ = v___y_883_;
v___y_783_ = v___y_884_;
v___y_784_ = v___y_885_;
v___y_785_ = v___y_886_;
goto v___jp_779_;
}
else
{
lean_object* v___x_897_; 
lean_dec(v___y_882_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v_env_679_);
lean_dec_ref(v_value_602_);
lean_dec_ref(v_type_601_);
lean_dec(v_levelParams_600_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 0);
lean_ctor_set(v___x_891_, 0, v_fst_893_);
v___x_897_ = v___x_891_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_fst_893_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_dec(v___x_888_);
v___y_780_ = v___y_880_;
v___y_781_ = v___y_882_;
v___y_782_ = v___y_883_;
v___y_783_ = v___y_884_;
v___y_784_ = v___y_885_;
v___y_785_ = v___y_886_;
goto v___jp_779_;
}
}
}
v___jp_900_:
{
if (v_cache_604_ == 0)
{
lean_object* v___x_904_; lean_object* v_a_905_; lean_object* v___f_906_; uint8_t v___x_907_; 
lean_dec(v___x_878_);
v___x_904_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_903_, v_a_611_);
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc_n(v_a_905_, 2);
lean_dec_ref(v___x_904_);
lean_inc(v_levelParams_600_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_906_, 0, v_a_905_);
lean_closure_set(v___f_906_, 1, v_levelParams_600_);
lean_closure_set(v___f_906_, 2, v___y_902_);
lean_inc_ref(v_env_679_);
v___x_907_ = l_Lean_Environment_hasUnsafe(v_env_679_, v_type_601_);
if (v___x_907_ == 0)
{
uint8_t v___x_908_; 
v___x_908_ = l_Lean_Environment_hasUnsafe(v_env_679_, v_value_602_);
v___y_861_ = v___f_906_;
v___y_862_ = v_a_905_;
v___y_863_ = v___x_908_;
goto v___jp_860_;
}
else
{
lean_dec_ref(v_env_679_);
v___y_861_ = v___f_906_;
v___y_862_ = v_a_905_;
v___y_863_ = v___x_907_;
goto v___jp_860_;
}
}
else
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v___x_878_, v___y_902_);
if (lean_obj_tag(v___x_909_) == 1)
{
lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_920_; 
v_val_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_920_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_fst_914_; lean_object* v_snd_915_; uint8_t v___x_916_; 
v_fst_914_ = lean_ctor_get(v_val_910_, 0);
lean_inc(v_fst_914_);
v_snd_915_ = lean_ctor_get(v_val_910_, 1);
lean_inc(v_snd_915_);
lean_dec(v_val_910_);
v___x_916_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__4(v_levelParams_600_, v_snd_915_);
lean_dec(v_snd_915_);
if (v___x_916_ == 0)
{
lean_dec(v_fst_914_);
lean_del_object(v___x_912_);
v___y_880_ = v___y_902_;
v___y_881_ = v___y_901_;
v___y_882_ = v___y_903_;
v___y_883_ = v_a_608_;
v___y_884_ = v_a_609_;
v___y_885_ = v_a_610_;
v___y_886_ = v_a_611_;
goto v___jp_879_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___x_878_);
lean_dec_ref(v_env_679_);
lean_dec_ref(v_value_602_);
lean_dec_ref(v_type_601_);
lean_dec(v_levelParams_600_);
if (v_isShared_913_ == 0)
{
lean_ctor_set_tag(v___x_912_, 0);
lean_ctor_set(v___x_912_, 0, v_fst_914_);
v___x_918_ = v___x_912_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_fst_914_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_dec(v___x_909_);
v___y_880_ = v___y_902_;
v___y_881_ = v___y_901_;
v___y_882_ = v___y_903_;
v___y_883_ = v_a_608_;
v___y_884_ = v_a_609_;
v___y_885_ = v_a_610_;
v___y_886_ = v_a_611_;
goto v___jp_879_;
}
}
}
v___jp_921_:
{
lean_object* v___x_923_; 
lean_inc_ref(v_type_601_);
v___x_923_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_923_, 0, v_type_601_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*1, v___y_922_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*1 + 1, v_defeq_607_);
if (lean_obj_tag(v_kind_x3f_603_) == 0)
{
lean_object* v___x_924_; 
v___x_924_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__1));
v___y_901_ = v___y_922_;
v___y_902_ = v___x_923_;
v___y_903_ = v___x_924_;
goto v___jp_900_;
}
else
{
lean_object* v_val_925_; 
v_val_925_ = lean_ctor_get(v_kind_x3f_603_, 0);
lean_inc(v_val_925_);
lean_dec_ref_known(v_kind_x3f_603_, 1);
v___y_901_ = v___y_922_;
v___y_902_ = v___x_923_;
v___y_903_ = v_val_925_;
goto v___jp_900_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkAuxLemma_0interp(lean_interpreter_value* stack)
{
lean_object* v_levelParams_600_ = stack[0].m_obj;
lean_object* v_type_601_ = stack[1].m_obj;
lean_object* v_value_602_ = stack[2].m_obj;
lean_object* v_kind_x3f_603_ = stack[3].m_obj;
uint8_t v_cache_604_ = stack[4].m_num;
uint8_t v_inferRfl_605_ = stack[5].m_num;
uint8_t v_forceExpose_606_ = stack[6].m_num;
uint8_t v_defeq_607_ = stack[7].m_num;
lean_object* v_a_608_ = stack[8].m_obj;
lean_object* v_a_609_ = stack[9].m_obj;
lean_object* v_a_610_ = stack[10].m_obj;
lean_object* v_a_611_ = stack[11].m_obj;
lean_object* v_res_927_;
v_res_927_ = l_Lean_Meta_mkAuxLemma(v_levelParams_600_, v_type_601_, v_value_602_, v_kind_x3f_603_, v_cache_604_, v_inferRfl_605_, v_forceExpose_606_, v_defeq_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_928_, lean_object* v_type_929_, lean_object* v_value_930_, lean_object* v_kind_x3f_931_, lean_object* v_cache_932_, lean_object* v_inferRfl_933_, lean_object* v_forceExpose_934_, lean_object* v_defeq_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
uint8_t v_cache_boxed_941_; uint8_t v_inferRfl_boxed_942_; uint8_t v_forceExpose_boxed_943_; uint8_t v_defeq_boxed_944_; lean_object* v_res_945_; 
v_cache_boxed_941_ = lean_unbox(v_cache_932_);
v_inferRfl_boxed_942_ = lean_unbox(v_inferRfl_933_);
v_forceExpose_boxed_943_ = lean_unbox(v_forceExpose_934_);
v_defeq_boxed_944_ = lean_unbox(v_defeq_935_);
v_res_945_ = l_Lean_Meta_mkAuxLemma(v_levelParams_928_, v_type_929_, v_value_930_, v_kind_x3f_931_, v_cache_boxed_941_, v_inferRfl_boxed_942_, v_forceExpose_boxed_943_, v_defeq_boxed_944_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_947_, v_x_948_, v_x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_00_u03b2_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___redArg(v_x_952_, v_x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_00_u03b2_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3(v_00_u03b2_955_, v_x_956_, v_x_957_);
lean_dec_ref(v_x_957_);
lean_dec_ref(v_x_956_);
return v_res_958_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_959_, lean_object* v_x_960_, size_t v_x_961_, size_t v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_960_, v_x_961_, v_x_962_, v_x_963_, v_x_964_);
return v___x_965_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_960_ = stack[1].m_obj;
size_t v_x_961_ = stack[2].m_num;
size_t v_x_962_ = stack[3].m_num;
lean_object* v_x_963_ = stack[4].m_obj;
lean_object* v_x_964_ = stack[5].m_obj;
lean_object* v_res_966_;
v_res_966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_box(0), v_x_960_, v_x_961_, v_x_962_, v_x_963_, v_x_964_);
stack->m_obj
 = v_res_966_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_967_, lean_object* v_x_968_, lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
size_t v_x_7458__boxed_973_; size_t v_x_7459__boxed_974_; lean_object* v_res_975_; 
v_x_7458__boxed_973_ = lean_unbox_usize(v_x_969_);
lean_dec(v_x_969_);
v_x_7459__boxed_974_ = lean_unbox_usize(v_x_970_);
lean_dec(v_x_970_);
v_res_975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_967_, v_x_968_, v_x_7458__boxed_973_, v_x_7459__boxed_974_, v_x_971_, v_x_972_);
return v_res_975_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b1_976_, lean_object* v_attrName_977_, lean_object* v_declName_978_, lean_object* v_asyncPrefix_x3f_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_attrName_977_, v_declName_978_, v_asyncPrefix_x3f_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
return v___x_985_;
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_977_ = stack[1].m_obj;
lean_object* v_declName_978_ = stack[2].m_obj;
lean_object* v_asyncPrefix_x3f_979_ = stack[3].m_obj;
lean_object* v___y_980_ = stack[4].m_obj;
lean_object* v___y_981_ = stack[5].m_obj;
lean_object* v___y_982_ = stack[6].m_obj;
lean_object* v___y_983_ = stack[7].m_obj;
lean_object* v_res_986_;
v_res_986_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_box(0), v_attrName_977_, v_declName_978_, v_asyncPrefix_x3f_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_987_, lean_object* v_attrName_988_, lean_object* v_declName_989_, lean_object* v_asyncPrefix_x3f_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b1_987_, v_attrName_988_, v_declName_989_, v_asyncPrefix_x3f_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_996_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(lean_object* v_00_u03b1_997_, lean_object* v_attrName_998_, lean_object* v_declName_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___redArg(v_attrName_998_, v_declName_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_998_ = stack[1].m_obj;
lean_object* v_declName_999_ = stack[2].m_obj;
lean_object* v___y_1000_ = stack[3].m_obj;
lean_object* v___y_1001_ = stack[4].m_obj;
lean_object* v___y_1002_ = stack[5].m_obj;
lean_object* v___y_1003_ = stack[6].m_obj;
lean_object* v_res_1006_;
v_res_1006_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(lean_box(0), v_attrName_998_, v_declName_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
stack->m_obj
 = v_res_1006_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1007_, lean_object* v_attrName_1008_, lean_object* v_declName_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__4(v_00_u03b1_1007_, v_attrName_1008_, v_declName_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1015_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_object* v_00_u03b2_1016_, lean_object* v_x_1017_, size_t v_x_1018_, lean_object* v_x_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___redArg(v_x_1017_, v_x_1018_, v_x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1017_ = stack[1].m_obj;
size_t v_x_1018_ = stack[2].m_num;
lean_object* v_x_1019_ = stack[3].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(lean_box(0), v_x_1017_, v_x_1018_, v_x_1019_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
size_t v_x_7542__boxed_1026_; lean_object* v_res_1027_; 
v_x_7542__boxed_1026_ = lean_unbox_usize(v_x_1024_);
lean_dec(v_x_1024_);
v_res_1027_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6(v_00_u03b2_1022_, v_x_1023_, v_x_7542__boxed_1026_, v_x_1025_);
lean_dec_ref(v_x_1025_);
lean_dec_ref(v_x_1023_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1028_, lean_object* v_n_1029_, lean_object* v_k_1030_, lean_object* v_v_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_1029_, v_k_1030_, v_v_1031_);
return v___x_1032_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1033_, size_t v_depth_1034_, lean_object* v_keys_1035_, lean_object* v_vals_1036_, lean_object* v_heq_1037_, lean_object* v_i_1038_, lean_object* v_entries_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_1034_, v_keys_1035_, v_vals_1036_, v_i_1038_, v_entries_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1034_ = stack[1].m_num;
lean_object* v_keys_1035_ = stack[2].m_obj;
lean_object* v_vals_1036_ = stack[3].m_obj;
lean_object* v_i_1038_ = stack[5].m_obj;
lean_object* v_entries_1039_ = stack[6].m_obj;
lean_object* v_res_1041_;
v_res_1041_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_box(0), v_depth_1034_, v_keys_1035_, v_vals_1036_, lean_box(0), v_i_1038_, v_entries_1039_);
stack->m_obj
 = v_res_1041_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1042_, lean_object* v_depth_1043_, lean_object* v_keys_1044_, lean_object* v_vals_1045_, lean_object* v_heq_1046_, lean_object* v_i_1047_, lean_object* v_entries_1048_){
_start:
{
size_t v_depth_boxed_1049_; lean_object* v_res_1050_; 
v_depth_boxed_1049_ = lean_unbox_usize(v_depth_1043_);
lean_dec(v_depth_1043_);
v_res_1050_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_1042_, v_depth_boxed_1049_, v_keys_1044_, v_vals_1045_, v_heq_1046_, v_i_1047_, v_entries_1048_);
lean_dec_ref(v_vals_1045_);
lean_dec_ref(v_keys_1044_);
return v_res_1050_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_1051_, lean_object* v_msg_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_msg_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1052_ = stack[1].m_obj;
lean_object* v___y_1053_ = stack[2].m_obj;
lean_object* v___y_1054_ = stack[3].m_obj;
lean_object* v___y_1055_ = stack[4].m_obj;
lean_object* v___y_1056_ = stack[5].m_obj;
lean_object* v_res_1059_;
v_res_1059_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_box(0), v_msg_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
stack->m_obj
 = v_res_1059_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1060_, lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b1_1060_, v_msg_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1068_, lean_object* v_keys_1069_, lean_object* v_vals_1070_, lean_object* v_heq_1071_, lean_object* v_i_1072_, lean_object* v_k_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___redArg(v_keys_1069_, v_vals_1070_, v_i_1072_, v_k_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1075_, lean_object* v_keys_1076_, lean_object* v_vals_1077_, lean_object* v_heq_1078_, lean_object* v_i_1079_, lean_object* v_k_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__3_spec__6_spec__10(v_00_u03b2_1075_, v_keys_1076_, v_vals_1077_, v_heq_1078_, v_i_1079_, v_k_1080_);
lean_dec_ref(v_k_1080_);
lean_dec_ref(v_vals_1077_);
lean_dec_ref(v_keys_1076_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__6___redArg(v_x_1083_, v_x_1084_, v_x_1085_, v_x_1086_);
return v___x_1087_;
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
