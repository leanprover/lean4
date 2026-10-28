// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Functions
// Imports: public import Lean.Meta.Sym.Arith.MonadRing public import Lean.Meta.Sym.Arith.MonadSemiring import Init.Grind.Ring
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__2_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__2_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__2_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__3_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__3_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__3_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__4_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Arith"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__4_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__4_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__5_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "checkedInstsExt"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__5_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__5_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__2_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__3_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__4_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(199, 78, 101, 187, 224, 73, 195, 34)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__5_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 148, 45, 23, 72, 132, 114, 16)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_checkedInstsExt;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "error while initializing arithmetic operators:\ninstance for `"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "\nis not definitionally equal to the expected one "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "\nwhen only reducible definitions and instances are reduced"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instHSMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 168, 246, 170, 1, 89, 173, 16)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "nsmul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 91, 174, 144, 107, 56, 221, 203)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "zsmul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(150, 37, 191, 247, 137, 26, 61, 190)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 4, 252, 84, 28, 16, 24, 6)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 152, 64, 108, 234, 163, 46, 107)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "internal error: type is not a field"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHDiv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 70, 113, 198, 157, 211, 131, 18)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toDiv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 88, 233, 125, 69, 12, 189, 21)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(232, 146, 236, 221, 122, 127, 105, 70)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg(){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___closed__1);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___dummy_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg();
return v_res_7_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___redArg();
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___closed__0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_(lean_object* v___x_11_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_st_mk_ref(v___x_11_);
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2____boxed(lean_object* v___x_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_(v___x_16_);
return v_res_18_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_19_; lean_object* v___f_20_; 
v___x_19_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__spec__0___closed__0);
v___f_20_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_20_, 0, v___x_19_);
return v___f_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; lean_object* v___x_38_; 
v___f_33_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_box(2);
v___x_36_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn___closed__6_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_));
v___x_37_ = 0;
v___x_38_ = l_Lean_registerEnvExtension___redArg(v___f_33_, v___x_34_, v___x_35_, v___x_36_, v___x_37_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2____boxed(lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_();
return v_res_40_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported___lam__0(lean_object* v_env_41_, uint8_t v___x_42_, lean_object* v_e_43_){
_start:
{
if (lean_obj_tag(v_e_43_) == 4)
{
lean_object* v_declName_44_; uint8_t v___x_45_; 
v_declName_44_ = lean_ctor_get(v_e_43_, 0);
v___x_45_ = l_Lean_Environment_isImportedConst(v_env_41_, v_declName_44_);
if (v___x_45_ == 0)
{
uint8_t v___x_46_; 
v___x_46_ = 1;
return v___x_46_;
}
else
{
return v___x_42_;
}
}
else
{
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported___lam__0___boxed(lean_object* v_env_47_, lean_object* v___x_48_, lean_object* v_e_49_){
_start:
{
uint8_t v___x_182__boxed_50_; uint8_t v_res_51_; lean_object* v_r_52_; 
v___x_182__boxed_50_ = lean_unbox(v___x_48_);
v_res_51_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported___lam__0(v_env_47_, v___x_182__boxed_50_, v_e_49_);
lean_dec_ref(v_e_49_);
lean_dec_ref(v_env_47_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported(lean_object* v_env_53_, lean_object* v_e_54_){
_start:
{
uint8_t v___x_55_; 
v___x_55_ = l_Lean_Expr_hasFVar(v_e_54_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; 
v___x_56_ = l_Lean_Expr_hasMVar(v_e_54_);
if (v___x_56_ == 0)
{
uint8_t v___x_57_; 
v___x_57_ = l_Lean_Expr_hasLevelParam(v_e_54_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___f_59_; lean_object* v___x_60_; 
v___x_58_ = lean_box(v___x_57_);
v___f_59_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported___lam__0___boxed), 3, 2);
lean_closure_set(v___f_59_, 0, v_env_53_);
lean_closure_set(v___f_59_, 1, v___x_58_);
v___x_60_ = lean_find_expr(v___f_59_, v_e_54_);
lean_dec_ref(v___f_59_);
if (lean_obj_tag(v___x_60_) == 0)
{
uint8_t v___x_61_; 
v___x_61_ = 1;
return v___x_61_;
}
else
{
lean_dec_ref_known(v___x_60_, 1);
return v___x_57_;
}
}
else
{
lean_dec_ref(v_env_53_);
return v___x_56_;
}
}
else
{
lean_dec_ref(v_env_53_);
return v___x_55_;
}
}
else
{
uint8_t v___x_62_; 
lean_dec_ref(v_env_53_);
v___x_62_ = 0;
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported___boxed(lean_object* v_env_63_, lean_object* v_e_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported(v_env_63_, v_e_64_);
lean_dec_ref(v_e_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7___redArg(lean_object* v_keys_67_, lean_object* v_i_68_, lean_object* v_k_69_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = lean_array_get_size(v_keys_67_);
v___x_75_ = lean_nat_dec_lt(v_i_68_, v___x_74_);
if (v___x_75_ == 0)
{
lean_dec(v_i_68_);
return v___x_75_;
}
else
{
lean_object* v_fst_76_; lean_object* v_snd_77_; lean_object* v_k_x27_78_; lean_object* v_fst_79_; lean_object* v_snd_80_; uint8_t v___x_81_; 
v_fst_76_ = lean_ctor_get(v_k_69_, 0);
v_snd_77_ = lean_ctor_get(v_k_69_, 1);
v_k_x27_78_ = lean_array_fget_borrowed(v_keys_67_, v_i_68_);
v_fst_79_ = lean_ctor_get(v_k_x27_78_, 0);
v_snd_80_ = lean_ctor_get(v_k_x27_78_, 1);
v___x_81_ = lean_expr_eqv(v_fst_76_, v_fst_79_);
if (v___x_81_ == 0)
{
goto v___jp_70_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = lean_expr_eqv(v_snd_77_, v_snd_80_);
if (v___x_82_ == 0)
{
goto v___jp_70_;
}
else
{
lean_dec(v_i_68_);
return v___x_75_;
}
}
}
v___jp_70_:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_i_68_, v___x_71_);
lean_dec(v_i_68_);
v_i_68_ = v___x_72_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_keys_83_, lean_object* v_i_84_, lean_object* v_k_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7___redArg(v_keys_83_, v_i_84_, v_k_85_);
lean_dec_ref(v_k_85_);
lean_dec_ref(v_keys_83_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4___redArg(lean_object* v_x_88_, size_t v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v_es_91_; lean_object* v___x_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v_j_95_; lean_object* v___x_96_; 
v_es_91_ = lean_ctor_get(v_x_88_, 0);
v___x_92_ = lean_box(2);
v___x_93_ = ((size_t)31ULL);
v___x_94_ = lean_usize_land(v_x_89_, v___x_93_);
v_j_95_ = lean_usize_to_nat(v___x_94_);
v___x_96_ = lean_array_get_borrowed(v___x_92_, v_es_91_, v_j_95_);
lean_dec(v_j_95_);
switch(lean_obj_tag(v___x_96_))
{
case 0:
{
lean_object* v_key_97_; lean_object* v_fst_98_; lean_object* v_snd_99_; lean_object* v_fst_100_; lean_object* v_snd_101_; uint8_t v___x_102_; 
v_key_97_ = lean_ctor_get(v___x_96_, 0);
v_fst_98_ = lean_ctor_get(v_x_90_, 0);
v_snd_99_ = lean_ctor_get(v_x_90_, 1);
v_fst_100_ = lean_ctor_get(v_key_97_, 0);
v_snd_101_ = lean_ctor_get(v_key_97_, 1);
v___x_102_ = lean_expr_eqv(v_fst_98_, v_fst_100_);
if (v___x_102_ == 0)
{
return v___x_102_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = lean_expr_eqv(v_snd_99_, v_snd_101_);
return v___x_103_;
}
}
case 1:
{
lean_object* v_node_104_; size_t v___x_105_; size_t v___x_106_; 
v_node_104_ = lean_ctor_get(v___x_96_, 0);
v___x_105_ = ((size_t)5ULL);
v___x_106_ = lean_usize_shift_right(v_x_89_, v___x_105_);
v_x_88_ = v_node_104_;
v_x_89_ = v___x_106_;
goto _start;
}
default: 
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
}
else
{
lean_object* v_ks_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_ks_109_ = lean_ctor_get(v_x_88_, 0);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7___redArg(v_ks_109_, v___x_110_, v_x_90_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4___redArg___boxed(lean_object* v_x_112_, lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
size_t v_x_3675__boxed_115_; uint8_t v_res_116_; lean_object* v_r_117_; 
v_x_3675__boxed_115_ = lean_unbox_usize(v_x_113_);
lean_dec(v_x_113_);
v_res_116_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4___redArg(v_x_112_, v_x_3675__boxed_115_, v_x_114_);
lean_dec_ref(v_x_114_);
lean_dec_ref(v_x_112_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2___redArg(lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
lean_object* v_fst_120_; lean_object* v_snd_121_; uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v___x_124_; size_t v___x_125_; uint8_t v___x_126_; 
v_fst_120_ = lean_ctor_get(v_x_119_, 0);
v_snd_121_ = lean_ctor_get(v_x_119_, 1);
v___x_122_ = l_Lean_Expr_hash(v_fst_120_);
v___x_123_ = l_Lean_Expr_hash(v_snd_121_);
v___x_124_ = lean_uint64_mix_hash(v___x_122_, v___x_123_);
v___x_125_ = lean_uint64_to_usize(v___x_124_);
v___x_126_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4___redArg(v_x_118_, v___x_125_, v_x_119_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2___redArg___boxed(lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2___redArg(v_x_127_, v_x_128_);
lean_dec_ref(v_x_128_);
lean_dec_ref(v_x_127_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1_spec__2(lean_object* v_msgData_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; lean_object* v_env_138_; uint8_t v___x_139_; lean_object* v_env_140_; lean_object* v___x_141_; lean_object* v_toCold_142_; lean_object* v_mctx_143_; lean_object* v_lctx_144_; lean_object* v_options_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_137_ = lean_st_ref_get(v___y_135_);
v_env_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc_ref(v_env_138_);
lean_dec(v___x_137_);
v___x_139_ = 0;
v_env_140_ = l_Lean_Environment_setRecordingDeps(v_env_138_, v___x_139_);
v___x_141_ = lean_st_ref_get(v___y_133_);
v_toCold_142_ = lean_ctor_get(v___y_134_, 0);
v_mctx_143_ = lean_ctor_get(v___x_141_, 0);
lean_inc_ref(v_mctx_143_);
lean_dec(v___x_141_);
v_lctx_144_ = lean_ctor_get(v___y_132_, 2);
v_options_145_ = lean_ctor_get(v_toCold_142_, 2);
lean_inc_ref(v_options_145_);
lean_inc_ref(v_lctx_144_);
v___x_146_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_146_, 0, v_env_140_);
lean_ctor_set(v___x_146_, 1, v_mctx_143_);
lean_ctor_set(v___x_146_, 2, v_lctx_144_);
lean_ctor_set(v___x_146_, 3, v_options_145_);
v___x_147_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_msgData_131_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1_spec__2___boxed(lean_object* v_msgData_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1_spec__2(v_msgData_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1___redArg(lean_object* v_msg_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_ref_162_; lean_object* v___x_163_; lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_172_; 
v_ref_162_ = lean_ctor_get(v___y_159_, 2);
v___x_163_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1_spec__2(v_msg_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_172_ == 0)
{
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_inc(v_ref_162_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v_ref_162_);
lean_ctor_set(v___x_168_, 1, v_a_164_);
if (v_isShared_167_ == 0)
{
lean_ctor_set_tag(v___x_166_, 1);
lean_ctor_set(v___x_166_, 0, v___x_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1___redArg___boxed(lean_object* v_msg_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1___redArg(v_msg_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_180_, lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
lean_object* v_ks_184_; lean_object* v_vs_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_217_; 
v_ks_184_ = lean_ctor_get(v_x_180_, 0);
v_vs_185_ = lean_ctor_get(v_x_180_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_x_180_);
if (v_isSharedCheck_217_ == 0)
{
v___x_187_ = v_x_180_;
v_isShared_188_ = v_isSharedCheck_217_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_vs_185_);
lean_inc(v_ks_184_);
lean_dec(v_x_180_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_217_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_array_get_size(v_ks_184_);
v___x_197_ = lean_nat_dec_lt(v_x_181_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
lean_del_object(v___x_187_);
lean_dec(v_x_181_);
v___x_198_ = lean_array_push(v_ks_184_, v_x_182_);
v___x_199_ = lean_array_push(v_vs_185_, v_x_183_);
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
return v___x_200_;
}
else
{
lean_object* v_fst_201_; lean_object* v_snd_202_; lean_object* v_k_x27_203_; lean_object* v_fst_204_; lean_object* v_snd_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_216_; 
v_fst_201_ = lean_ctor_get(v_x_182_, 0);
v_snd_202_ = lean_ctor_get(v_x_182_, 1);
v_k_x27_203_ = lean_array_fget(v_ks_184_, v_x_181_);
v_fst_204_ = lean_ctor_get(v_k_x27_203_, 0);
v_snd_205_ = lean_ctor_get(v_k_x27_203_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_k_x27_203_);
if (v_isSharedCheck_216_ == 0)
{
v___x_207_ = v_k_x27_203_;
v_isShared_208_ = v_isSharedCheck_216_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_snd_205_);
lean_inc(v_fst_204_);
lean_dec(v_k_x27_203_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_216_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
uint8_t v___x_209_; 
v___x_209_ = lean_expr_eqv(v_fst_201_, v_fst_204_);
lean_dec(v_fst_204_);
if (v___x_209_ == 0)
{
lean_del_object(v___x_207_);
lean_dec(v_snd_205_);
goto v___jp_189_;
}
else
{
uint8_t v___x_210_; 
v___x_210_ = lean_expr_eqv(v_snd_202_, v_snd_205_);
lean_dec(v_snd_205_);
if (v___x_210_ == 0)
{
lean_del_object(v___x_207_);
goto v___jp_189_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
lean_del_object(v___x_187_);
v___x_211_ = lean_array_fset(v_ks_184_, v_x_181_, v_x_182_);
v___x_212_ = lean_array_fset(v_vs_185_, v_x_181_, v_x_183_);
lean_dec(v_x_181_);
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 1);
lean_ctor_set(v___x_207_, 1, v___x_212_);
lean_ctor_set(v___x_207_, 0, v___x_211_);
v___x_214_ = v___x_207_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
v___jp_189_:
{
lean_object* v___x_191_; 
if (v_isShared_188_ == 0)
{
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_ks_184_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_vs_185_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_nat_add(v_x_181_, v___x_192_);
lean_dec(v_x_181_);
v_x_180_ = v___x_191_;
v_x_181_ = v___x_193_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1___redArg(lean_object* v_n_218_, lean_object* v_k_219_, lean_object* v_v_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1_spec__5___redArg(v_n_218_, v___x_221_, v_k_219_, v_v_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg(lean_object* v_x_224_, size_t v_x_225_, size_t v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_object* v_es_229_; size_t v___x_230_; size_t v___x_231_; lean_object* v_j_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_es_229_ = lean_ctor_get(v_x_224_, 0);
v___x_230_ = ((size_t)31ULL);
v___x_231_ = lean_usize_land(v_x_225_, v___x_230_);
v_j_232_ = lean_usize_to_nat(v___x_231_);
v___x_233_ = lean_array_get_size(v_es_229_);
v___x_234_ = lean_nat_dec_lt(v_j_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec(v_j_232_);
lean_dec(v_x_228_);
lean_dec_ref(v_x_227_);
return v_x_224_;
}
else
{
lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_279_; 
lean_inc_ref(v_es_229_);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v_x_224_, 0);
lean_dec(v_unused_280_);
v___x_236_ = v_x_224_;
v_isShared_237_ = v_isSharedCheck_279_;
goto v_resetjp_235_;
}
else
{
lean_dec(v_x_224_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_279_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_v_238_; lean_object* v___x_239_; lean_object* v_xs_x27_240_; lean_object* v___y_242_; 
v_v_238_ = lean_array_fget(v_es_229_, v_j_232_);
v___x_239_ = lean_box(0);
v_xs_x27_240_ = lean_array_fset(v_es_229_, v_j_232_, v___x_239_);
switch(lean_obj_tag(v_v_238_))
{
case 0:
{
lean_object* v_key_247_; lean_object* v_val_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_264_; 
v_key_247_ = lean_ctor_get(v_v_238_, 0);
v_val_248_ = lean_ctor_get(v_v_238_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_v_238_);
if (v_isSharedCheck_264_ == 0)
{
v___x_250_ = v_v_238_;
v_isShared_251_ = v_isSharedCheck_264_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_val_248_);
lean_inc(v_key_247_);
lean_dec(v_v_238_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_264_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v_fst_255_; lean_object* v_snd_256_; lean_object* v_fst_257_; lean_object* v_snd_258_; uint8_t v___x_259_; 
v_fst_255_ = lean_ctor_get(v_x_227_, 0);
v_snd_256_ = lean_ctor_get(v_x_227_, 1);
v_fst_257_ = lean_ctor_get(v_key_247_, 0);
v_snd_258_ = lean_ctor_get(v_key_247_, 1);
v___x_259_ = lean_expr_eqv(v_fst_255_, v_fst_257_);
if (v___x_259_ == 0)
{
lean_del_object(v___x_250_);
goto v___jp_252_;
}
else
{
uint8_t v___x_260_; 
v___x_260_ = lean_expr_eqv(v_snd_256_, v_snd_258_);
if (v___x_260_ == 0)
{
lean_del_object(v___x_250_);
goto v___jp_252_;
}
else
{
lean_object* v___x_262_; 
lean_dec(v_val_248_);
lean_dec(v_key_247_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v_x_228_);
lean_ctor_set(v___x_250_, 0, v_x_227_);
v___x_262_ = v___x_250_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_x_227_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_x_228_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
v___y_242_ = v___x_262_;
goto v___jp_241_;
}
}
}
v___jp_252_:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_247_, v_val_248_, v_x_227_, v_x_228_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
v___y_242_ = v___x_254_;
goto v___jp_241_;
}
}
}
case 1:
{
lean_object* v_node_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_277_; 
v_node_265_ = lean_ctor_get(v_v_238_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_v_238_);
if (v_isSharedCheck_277_ == 0)
{
v___x_267_ = v_v_238_;
v_isShared_268_ = v_isSharedCheck_277_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_node_265_);
lean_dec(v_v_238_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_277_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_269_ = ((size_t)5ULL);
v___x_270_ = lean_usize_shift_right(v_x_225_, v___x_269_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_add(v_x_226_, v___x_271_);
v___x_273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg(v_node_265_, v___x_270_, v___x_272_, v_x_227_, v_x_228_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_273_);
v___x_275_ = v___x_267_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
v___y_242_ = v___x_275_;
goto v___jp_241_;
}
}
}
default: 
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v_x_227_);
lean_ctor_set(v___x_278_, 1, v_x_228_);
v___y_242_ = v___x_278_;
goto v___jp_241_;
}
}
v___jp_241_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_array_fset(v_xs_x27_240_, v_j_232_, v___y_242_);
lean_dec(v_j_232_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_243_);
v___x_245_ = v___x_236_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
else
{
lean_object* v_ks_281_; lean_object* v_vs_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_300_; 
v_ks_281_ = lean_ctor_get(v_x_224_, 0);
v_vs_282_ = lean_ctor_get(v_x_224_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_300_ == 0)
{
v___x_284_ = v_x_224_;
v_isShared_285_ = v_isSharedCheck_300_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_vs_282_);
lean_inc(v_ks_281_);
lean_dec(v_x_224_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_300_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_ks_281_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_vs_282_);
v___x_287_ = v_reuseFailAlloc_299_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v_newNode_288_; size_t v___x_289_; uint8_t v___x_290_; 
v_newNode_288_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1___redArg(v___x_287_, v_x_227_, v_x_228_);
v___x_289_ = ((size_t)7ULL);
v___x_290_ = lean_usize_dec_le(v___x_289_, v_x_226_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_291_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_288_);
v___x_292_ = lean_unsigned_to_nat(4u);
v___x_293_ = lean_nat_dec_lt(v___x_291_, v___x_292_);
lean_dec(v___x_291_);
if (v___x_293_ == 0)
{
lean_object* v_ks_294_; lean_object* v_vs_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_ks_294_ = lean_ctor_get(v_newNode_288_, 0);
lean_inc_ref(v_ks_294_);
v_vs_295_ = lean_ctor_get(v_newNode_288_, 1);
lean_inc_ref(v_vs_295_);
lean_dec_ref(v_newNode_288_);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg___closed__0);
v___x_298_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2___redArg(v_x_226_, v_ks_294_, v_vs_295_, v___x_296_, v___x_297_);
lean_dec_ref(v_vs_295_);
lean_dec_ref(v_ks_294_);
return v___x_298_;
}
else
{
return v_newNode_288_;
}
}
else
{
return v_newNode_288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2___redArg(size_t v_depth_301_, lean_object* v_keys_302_, lean_object* v_vals_303_, lean_object* v_i_304_, lean_object* v_entries_305_){
_start:
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_array_get_size(v_keys_302_);
v___x_307_ = lean_nat_dec_lt(v_i_304_, v___x_306_);
if (v___x_307_ == 0)
{
lean_dec(v_i_304_);
return v_entries_305_;
}
else
{
lean_object* v_k_308_; lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v_v_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; size_t v_h_315_; size_t v___x_316_; lean_object* v___x_317_; size_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v_h_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_k_308_ = lean_array_fget_borrowed(v_keys_302_, v_i_304_);
v_fst_309_ = lean_ctor_get(v_k_308_, 0);
v_snd_310_ = lean_ctor_get(v_k_308_, 1);
v_v_311_ = lean_array_fget_borrowed(v_vals_303_, v_i_304_);
v___x_312_ = l_Lean_Expr_hash(v_fst_309_);
v___x_313_ = l_Lean_Expr_hash(v_snd_310_);
v___x_314_ = lean_uint64_mix_hash(v___x_312_, v___x_313_);
v_h_315_ = lean_uint64_to_usize(v___x_314_);
v___x_316_ = ((size_t)5ULL);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_sub(v_depth_301_, v___x_318_);
v___x_320_ = lean_usize_mul(v___x_316_, v___x_319_);
v_h_321_ = lean_usize_shift_right(v_h_315_, v___x_320_);
v___x_322_ = lean_nat_add(v_i_304_, v___x_317_);
lean_dec(v_i_304_);
lean_inc(v_v_311_);
lean_inc(v_k_308_);
v___x_323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg(v_entries_305_, v_h_321_, v_depth_301_, v_k_308_, v_v_311_);
v_i_304_ = v___x_322_;
v_entries_305_ = v___x_323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_325_, lean_object* v_keys_326_, lean_object* v_vals_327_, lean_object* v_i_328_, lean_object* v_entries_329_){
_start:
{
size_t v_depth_boxed_330_; lean_object* v_res_331_; 
v_depth_boxed_330_ = lean_unbox_usize(v_depth_325_);
lean_dec(v_depth_325_);
v_res_331_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2___redArg(v_depth_boxed_330_, v_keys_326_, v_vals_327_, v_i_328_, v_entries_329_);
lean_dec_ref(v_vals_327_);
lean_dec_ref(v_keys_326_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg___boxed(lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
size_t v_x_3904__boxed_337_; size_t v_x_3905__boxed_338_; lean_object* v_res_339_; 
v_x_3904__boxed_337_ = lean_unbox_usize(v_x_333_);
lean_dec(v_x_333_);
v_x_3905__boxed_338_ = lean_unbox_usize(v_x_334_);
lean_dec(v_x_334_);
v_res_339_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg(v_x_332_, v_x_3904__boxed_337_, v_x_3905__boxed_338_, v_x_335_, v_x_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v_fst_343_; lean_object* v_snd_344_; uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v___x_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v___x_350_; 
v_fst_343_ = lean_ctor_get(v_x_341_, 0);
v_snd_344_ = lean_ctor_get(v_x_341_, 1);
v___x_345_ = l_Lean_Expr_hash(v_fst_343_);
v___x_346_ = l_Lean_Expr_hash(v_snd_344_);
v___x_347_ = lean_uint64_mix_hash(v___x_345_, v___x_346_);
v___x_348_ = lean_uint64_to_usize(v___x_347_);
v___x_349_ = ((size_t)1ULL);
v___x_350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg(v_x_340_, v___x_348_, v___x_349_, v_x_341_, v_x_342_);
return v___x_350_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2));
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object* v_declName_363_, lean_object* v_inst_364_, lean_object* v_inst_x27_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
uint8_t v___y_375_; lean_object* v___y_376_; lean_object* v___y_391_; lean_object* v___y_392_; uint8_t v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; uint8_t v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v_env_450_; uint8_t v___y_452_; uint8_t v___x_471_; 
v___x_448_ = lean_box(0);
v___x_449_ = lean_st_ref_get(v_a_369_);
v_env_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc_ref_n(v_env_450_, 2);
lean_dec(v___x_449_);
v___x_471_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported(v_env_450_, v_inst_364_);
if (v___x_471_ == 0)
{
v___y_452_ = v___x_471_;
goto v___jp_451_;
}
else
{
uint8_t v___x_472_; 
lean_inc_ref(v_env_450_);
v___x_472_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_isClosedImported(v_env_450_, v_inst_x27_365_);
v___y_452_ = v___x_472_;
goto v___jp_451_;
}
v___jp_371_:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_box(0);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
v___jp_374_:
{
if (v___y_375_ == 1)
{
if (lean_obj_tag(v___y_376_) == 1)
{
lean_object* v_val_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_389_; 
v_val_377_ = lean_ctor_get(v___y_376_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___y_376_);
if (v_isSharedCheck_389_ == 0)
{
v___x_379_ = v___y_376_;
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_val_377_);
lean_dec(v___y_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_381_ = lean_st_ref_take(v_val_377_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v_inst_364_);
lean_ctor_set(v___x_382_, 1, v_inst_x27_365_);
v___x_383_ = lean_box(0);
v___x_384_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v___x_381_, v___x_382_, v___x_383_);
v___x_385_ = lean_st_ref_put(v_val_377_, v___x_384_);
lean_dec(v_val_377_);
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 0);
lean_ctor_set(v___x_379_, 0, v___x_385_);
v___x_387_ = v___x_379_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
else
{
lean_dec(v___y_376_);
lean_dec_ref(v_inst_x27_365_);
lean_dec_ref(v_inst_364_);
goto v___jp_371_;
}
}
else
{
lean_dec(v___y_376_);
lean_dec_ref(v_inst_x27_365_);
lean_dec_ref(v_inst_364_);
goto v___jp_371_;
}
}
v___jp_390_:
{
if (lean_obj_tag(v___y_397_) == 0)
{
lean_object* v_a_398_; uint8_t v___x_399_; 
v_a_398_ = lean_ctor_get(v___y_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___y_397_, 1);
v___x_399_ = lean_unbox(v_a_398_);
lean_dec(v_a_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v___y_394_);
v___x_400_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1);
v___x_401_ = l_Lean_MessageData_ofName(v_declName_363_);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3);
v___x_404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = l_Lean_indentExpr(v_inst_364_);
v___x_406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = l_Lean_indentExpr(v_inst_x27_365_);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1___redArg(v___x_412_, v___y_395_, v___y_392_, v___y_391_, v___y_396_);
return v___x_413_;
}
else
{
lean_dec(v_declName_363_);
v___y_375_ = v___y_393_;
v___y_376_ = v___y_394_;
goto v___jp_374_;
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v___y_394_);
lean_dec_ref(v_inst_x27_365_);
lean_dec_ref(v_inst_364_);
lean_dec(v_declName_363_);
v_a_414_ = lean_ctor_get(v___y_397_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___y_397_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___y_397_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___y_397_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
v___jp_422_:
{
lean_object* v___x_429_; uint8_t v_transparency_430_; uint8_t v___x_431_; uint8_t v___x_432_; 
v___x_429_ = l_Lean_Meta_Context_config(v___y_425_);
v_transparency_430_ = lean_ctor_get_uint8(v___x_429_, 9);
lean_dec_ref(v___x_429_);
v___x_431_ = 3;
v___x_432_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v_keyedConfig_433_; uint8_t v_trackZetaDelta_434_; lean_object* v_zetaDeltaSet_435_; lean_object* v_lctx_436_; lean_object* v_localInstances_437_; lean_object* v_defEqCtx_x3f_438_; lean_object* v_synthPendingDepth_439_; lean_object* v_customCanUnfoldPredicate_x3f_440_; uint8_t v_univApprox_441_; uint8_t v_inTypeClassResolution_442_; uint8_t v_cacheInferType_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_keyedConfig_433_ = lean_ctor_get(v___y_425_, 0);
v_trackZetaDelta_434_ = lean_ctor_get_uint8(v___y_425_, sizeof(void*)*7);
v_zetaDeltaSet_435_ = lean_ctor_get(v___y_425_, 1);
v_lctx_436_ = lean_ctor_get(v___y_425_, 2);
v_localInstances_437_ = lean_ctor_get(v___y_425_, 3);
v_defEqCtx_x3f_438_ = lean_ctor_get(v___y_425_, 4);
v_synthPendingDepth_439_ = lean_ctor_get(v___y_425_, 5);
v_customCanUnfoldPredicate_x3f_440_ = lean_ctor_get(v___y_425_, 6);
v_univApprox_441_ = lean_ctor_get_uint8(v___y_425_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_442_ = lean_ctor_get_uint8(v___y_425_, sizeof(void*)*7 + 2);
v_cacheInferType_443_ = lean_ctor_get_uint8(v___y_425_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_433_);
v___x_444_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_431_, v_keyedConfig_433_);
lean_inc(v_customCanUnfoldPredicate_x3f_440_);
lean_inc(v_synthPendingDepth_439_);
lean_inc(v_defEqCtx_x3f_438_);
lean_inc_ref(v_localInstances_437_);
lean_inc_ref(v_lctx_436_);
lean_inc(v_zetaDeltaSet_435_);
v___x_445_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_zetaDeltaSet_435_);
lean_ctor_set(v___x_445_, 2, v_lctx_436_);
lean_ctor_set(v___x_445_, 3, v_localInstances_437_);
lean_ctor_set(v___x_445_, 4, v_defEqCtx_x3f_438_);
lean_ctor_set(v___x_445_, 5, v_synthPendingDepth_439_);
lean_ctor_set(v___x_445_, 6, v_customCanUnfoldPredicate_x3f_440_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*7, v_trackZetaDelta_434_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*7 + 1, v_univApprox_441_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*7 + 2, v_inTypeClassResolution_442_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*7 + 3, v_cacheInferType_443_);
lean_inc_ref(v_inst_x27_365_);
lean_inc_ref(v_inst_364_);
v___x_446_ = l_Lean_Meta_isExprDefEq(v_inst_364_, v_inst_x27_365_, v___x_445_, v___y_426_, v___y_427_, v___y_428_);
lean_dec_ref_known(v___x_445_, 7);
v___y_391_ = v___y_427_;
v___y_392_ = v___y_426_;
v___y_393_ = v___y_423_;
v___y_394_ = v___y_424_;
v___y_395_ = v___y_425_;
v___y_396_ = v___y_428_;
v___y_397_ = v___x_446_;
goto v___jp_390_;
}
else
{
lean_object* v___x_447_; 
lean_inc_ref(v_inst_x27_365_);
lean_inc_ref(v_inst_364_);
v___x_447_ = l_Lean_Meta_isExprDefEq(v_inst_364_, v_inst_x27_365_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
v___y_391_ = v___y_427_;
v___y_392_ = v___y_426_;
v___y_393_ = v___y_423_;
v___y_394_ = v___y_424_;
v___y_395_ = v___y_425_;
v___y_396_ = v___y_428_;
v___y_397_ = v___x_447_;
goto v___jp_390_;
}
}
v___jp_451_:
{
lean_object* v___x_453_; lean_object* v_asyncMode_454_; lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; 
v___x_453_ = l_Lean_Meta_Sym_Arith_checkedInstsExt;
v_asyncMode_454_ = lean_ctor_get(v___x_453_, 2);
v___x_455_ = lean_box(0);
v___x_456_ = 0;
v___x_457_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_448_, v___x_453_, v_env_450_, v_asyncMode_454_, v___x_455_, v___x_456_);
if (v___y_452_ == 1)
{
if (lean_obj_tag(v___x_457_) == 1)
{
lean_object* v_val_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_val_458_ = lean_ctor_get(v___x_457_, 0);
v___x_459_ = lean_st_ref_get(v_val_458_);
lean_inc_ref(v_inst_x27_365_);
lean_inc_ref(v_inst_364_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v_inst_364_);
lean_ctor_set(v___x_460_, 1, v_inst_x27_365_);
v___x_461_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2___redArg(v___x_459_, v___x_460_);
lean_dec_ref_known(v___x_460_, 2);
lean_dec(v___x_459_);
if (v___x_461_ == 0)
{
v___y_423_ = v___y_452_;
v___y_424_ = v___x_457_;
v___y_425_ = v_a_366_;
v___y_426_ = v_a_367_;
v___y_427_ = v_a_368_;
v___y_428_ = v_a_369_;
goto v___jp_422_;
}
else
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
lean_dec_ref(v_inst_x27_365_);
lean_dec_ref(v_inst_364_);
lean_dec(v_declName_363_);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v___x_457_, 0);
lean_dec(v_unused_470_);
v___x_463_ = v___x_457_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_dec(v___x_457_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = lean_box(0);
if (v_isShared_464_ == 0)
{
lean_ctor_set_tag(v___x_463_, 0);
lean_ctor_set(v___x_463_, 0, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
v___y_423_ = v___y_452_;
v___y_424_ = v___x_457_;
v___y_425_ = v_a_366_;
v___y_426_ = v_a_367_;
v___y_427_ = v_a_368_;
v___y_428_ = v_a_369_;
goto v___jp_422_;
}
}
else
{
v___y_423_ = v___y_452_;
v___y_424_ = v___x_457_;
v___y_425_ = v_a_366_;
v___y_426_ = v_a_367_;
v___y_427_ = v_a_368_;
v___y_428_ = v_a_369_;
goto v___jp_422_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed(lean_object* v_declName_473_, lean_object* v_inst_474_, lean_object* v_inst_x27_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_473_, v_inst_474_, v_inst_x27_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(lean_object* v_00_u03b2_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_x_483_, v_x_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1(lean_object* v_00_u03b1_487_, lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1___redArg(v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1___boxed(lean_object* v_00_u03b1_495_, lean_object* v_msg_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__1(v_00_u03b1_495_, v_msg_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
return v_res_502_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2(lean_object* v_00_u03b2_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2___redArg(v_x_504_, v_x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2___boxed(lean_object* v_00_u03b2_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2(v_00_u03b2_507_, v_x_508_, v_x_509_);
lean_dec_ref(v_x_509_);
lean_dec_ref(v_x_508_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(lean_object* v_00_u03b2_512_, lean_object* v_x_513_, size_t v_x_514_, size_t v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___redArg(v_x_513_, v_x_514_, v_x_515_, v_x_516_, v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_519_, lean_object* v_x_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
size_t v_x_4344__boxed_525_; size_t v_x_4345__boxed_526_; lean_object* v_res_527_; 
v_x_4344__boxed_525_ = lean_unbox_usize(v_x_521_);
lean_dec(v_x_521_);
v_x_4345__boxed_526_ = lean_unbox_usize(v_x_522_);
lean_dec(v_x_522_);
v_res_527_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0(v_00_u03b2_519_, v_x_520_, v_x_4344__boxed_525_, v_x_4345__boxed_526_, v_x_523_, v_x_524_);
return v_res_527_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4(lean_object* v_00_u03b2_528_, lean_object* v_x_529_, size_t v_x_530_, lean_object* v_x_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4___redArg(v_x_529_, v_x_530_, v_x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4___boxed(lean_object* v_00_u03b2_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
size_t v_x_4361__boxed_537_; uint8_t v_res_538_; lean_object* v_r_539_; 
v_x_4361__boxed_537_ = lean_unbox_usize(v_x_535_);
lean_dec(v_x_535_);
v_res_538_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4(v_00_u03b2_533_, v_x_534_, v_x_4361__boxed_537_, v_x_536_);
lean_dec_ref(v_x_536_);
lean_dec_ref(v_x_534_);
v_r_539_ = lean_box(v_res_538_);
return v_r_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_540_, lean_object* v_n_541_, lean_object* v_k_542_, lean_object* v_v_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1___redArg(v_n_541_, v_k_542_, v_v_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_545_, size_t v_depth_546_, lean_object* v_keys_547_, lean_object* v_vals_548_, lean_object* v_heq_549_, lean_object* v_i_550_, lean_object* v_entries_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2___redArg(v_depth_546_, v_keys_547_, v_vals_548_, v_i_550_, v_entries_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_553_, lean_object* v_depth_554_, lean_object* v_keys_555_, lean_object* v_vals_556_, lean_object* v_heq_557_, lean_object* v_i_558_, lean_object* v_entries_559_){
_start:
{
size_t v_depth_boxed_560_; lean_object* v_res_561_; 
v_depth_boxed_560_ = lean_unbox_usize(v_depth_554_);
lean_dec(v_depth_554_);
v_res_561_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__2(v_00_u03b2_553_, v_depth_boxed_560_, v_keys_555_, v_vals_556_, v_heq_557_, v_i_558_, v_entries_559_);
lean_dec_ref(v_vals_556_);
lean_dec_ref(v_keys_555_);
return v_res_561_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_562_, lean_object* v_keys_563_, lean_object* v_vals_564_, lean_object* v_heq_565_, lean_object* v_i_566_, lean_object* v_k_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7___redArg(v_keys_563_, v_i_566_, v_k_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_569_, lean_object* v_keys_570_, lean_object* v_vals_571_, lean_object* v_heq_572_, lean_object* v_i_573_, lean_object* v_k_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__2_spec__4_spec__7(v_00_u03b2_569_, v_keys_570_, v_vals_571_, v_heq_572_, v_i_573_, v_k_574_);
lean_dec_ref(v_k_574_);
lean_dec_ref(v_vals_571_);
lean_dec_ref(v_keys_570_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0_spec__0_spec__1_spec__5___redArg(v_x_578_, v_x_579_, v_x_580_, v_x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(lean_object* v_inst_583_, lean_object* v_declName_584_, lean_object* v___x_585_, lean_object* v_type_586_, lean_object* v_inst_587_, lean_object* v_____r_588_){
_start:
{
lean_object* v_canonExpr_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_canonExpr_589_ = lean_ctor_get(v_inst_583_, 0);
lean_inc(v_canonExpr_589_);
lean_dec_ref(v_inst_583_);
v___x_590_ = l_Lean_mkConst(v_declName_584_, v___x_585_);
v___x_591_ = l_Lean_mkAppB(v___x_590_, v_type_586_, v_inst_587_);
v___x_592_ = lean_apply_1(v_canonExpr_589_, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(lean_object* v_inst_593_, lean_object* v_declName_594_, lean_object* v___x_595_, lean_object* v_type_596_, lean_object* v_expectedInst_597_, lean_object* v_inst_598_, lean_object* v_toBind_599_, lean_object* v_inst_600_){
_start:
{
lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_inc_ref(v_inst_600_);
lean_inc(v_declName_594_);
v___f_601_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_601_, 0, v_inst_593_);
lean_closure_set(v___f_601_, 1, v_declName_594_);
lean_closure_set(v___f_601_, 2, v___x_595_);
lean_closure_set(v___f_601_, 3, v_type_596_);
lean_closure_set(v___f_601_, 4, v_inst_600_);
v___x_602_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_602_, 0, v_declName_594_);
lean_closure_set(v___x_602_, 1, v_inst_600_);
lean_closure_set(v___x_602_, 2, v_expectedInst_597_);
v___x_603_ = lean_apply_2(v_inst_598_, lean_box(0), v___x_602_);
v___x_604_ = lean_apply_4(v_toBind_599_, lean_box(0), lean_box(0), v___x_603_, v___f_601_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_type_609_, lean_object* v_u_610_, lean_object* v_instDeclName_611_, lean_object* v_declName_612_, lean_object* v_expectedInst_613_){
_start:
{
lean_object* v_toBind_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_toBind_614_ = lean_ctor_get(v_inst_607_, 1);
lean_inc_n(v_toBind_614_, 2);
v___x_615_ = lean_box(0);
v___x_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_616_, 0, v_u_610_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
lean_inc_ref(v_type_609_);
lean_inc_ref(v___x_616_);
lean_inc_ref(v_inst_608_);
v___f_617_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_617_, 0, v_inst_608_);
lean_closure_set(v___f_617_, 1, v_declName_612_);
lean_closure_set(v___f_617_, 2, v___x_616_);
lean_closure_set(v___f_617_, 3, v_type_609_);
lean_closure_set(v___f_617_, 4, v_expectedInst_613_);
lean_closure_set(v___f_617_, 5, v_inst_605_);
lean_closure_set(v___f_617_, 6, v_toBind_614_);
v___x_618_ = l_Lean_mkConst(v_instDeclName_611_, v___x_616_);
v___x_619_ = l_Lean_Expr_app___override(v___x_618_, v_type_609_);
v___x_620_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_607_, v_inst_606_, v_inst_608_, v___x_619_);
v___x_621_ = lean_apply_4(v_toBind_614_, lean_box(0), lean_box(0), v___x_620_, v___f_617_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(lean_object* v_m_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_type_627_, lean_object* v_u_628_, lean_object* v_instDeclName_629_, lean_object* v_declName_630_, lean_object* v_expectedInst_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_623_, v_inst_624_, v_inst_625_, v_inst_626_, v_type_627_, v_u_628_, v_instDeclName_629_, v_declName_630_, v_expectedInst_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0(lean_object* v_inst_633_, lean_object* v_declName_634_, lean_object* v___x_635_, lean_object* v_type_636_, lean_object* v_inst_637_, lean_object* v_____r_638_){
_start:
{
lean_object* v_canonExpr_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_canonExpr_639_ = lean_ctor_get(v_inst_633_, 0);
lean_inc(v_canonExpr_639_);
lean_dec_ref(v_inst_633_);
v___x_640_ = l_Lean_mkConst(v_declName_634_, v___x_635_);
lean_inc_ref_n(v_type_636_, 2);
v___x_641_ = l_Lean_mkApp4(v___x_640_, v_type_636_, v_type_636_, v_type_636_, v_inst_637_);
v___x_642_ = lean_apply_1(v_canonExpr_639_, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(lean_object* v_inst_643_, lean_object* v_declName_644_, lean_object* v___x_645_, lean_object* v_type_646_, lean_object* v_expectedInst_647_, lean_object* v_inst_648_, lean_object* v_toBind_649_, lean_object* v_inst_650_){
_start:
{
lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc_ref(v_inst_650_);
lean_inc(v_declName_644_);
v___f_651_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_651_, 0, v_inst_643_);
lean_closure_set(v___f_651_, 1, v_declName_644_);
lean_closure_set(v___f_651_, 2, v___x_645_);
lean_closure_set(v___f_651_, 3, v_type_646_);
lean_closure_set(v___f_651_, 4, v_inst_650_);
v___x_652_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_652_, 0, v_declName_644_);
lean_closure_set(v___x_652_, 1, v_inst_650_);
lean_closure_set(v___x_652_, 2, v_expectedInst_647_);
v___x_653_ = lean_apply_2(v_inst_648_, lean_box(0), v___x_652_);
v___x_654_ = lean_apply_4(v_toBind_649_, lean_box(0), lean_box(0), v___x_653_, v___f_651_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_type_659_, lean_object* v_u_660_, lean_object* v_instDeclName_661_, lean_object* v_declName_662_, lean_object* v_expectedInst_663_){
_start:
{
lean_object* v_toBind_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___f_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_toBind_664_ = lean_ctor_get(v_inst_657_, 1);
lean_inc_n(v_toBind_664_, 2);
v___x_665_ = lean_box(0);
lean_inc_n(v_u_660_, 2);
v___x_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_666_, 0, v_u_660_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_667_, 0, v_u_660_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_668_, 0, v_u_660_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
lean_inc_ref_n(v_type_659_, 3);
lean_inc_ref(v___x_668_);
lean_inc_ref(v_inst_658_);
v___f_669_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_669_, 0, v_inst_658_);
lean_closure_set(v___f_669_, 1, v_declName_662_);
lean_closure_set(v___f_669_, 2, v___x_668_);
lean_closure_set(v___f_669_, 3, v_type_659_);
lean_closure_set(v___f_669_, 4, v_expectedInst_663_);
lean_closure_set(v___f_669_, 5, v_inst_655_);
lean_closure_set(v___f_669_, 6, v_toBind_664_);
v___x_670_ = l_Lean_mkConst(v_instDeclName_661_, v___x_668_);
v___x_671_ = l_Lean_mkApp3(v___x_670_, v_type_659_, v_type_659_, v_type_659_);
v___x_672_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_657_, v_inst_656_, v_inst_658_, v___x_671_);
v___x_673_ = lean_apply_4(v_toBind_664_, lean_box(0), lean_box(0), v___x_672_, v___f_669_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(lean_object* v_m_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_type_679_, lean_object* v_u_680_, lean_object* v_instDeclName_681_, lean_object* v_declName_682_, lean_object* v_expectedInst_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_675_, v_inst_676_, v_inst_677_, v_inst_678_, v_type_679_, v_u_680_, v_instDeclName_681_, v_declName_682_, v_expectedInst_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0(lean_object* v_inst_685_, lean_object* v___x_686_, lean_object* v___x_687_, lean_object* v_type_688_, lean_object* v___x_689_, lean_object* v_inst_690_, lean_object* v_____r_691_){
_start:
{
lean_object* v_canonExpr_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_canonExpr_692_ = lean_ctor_get(v_inst_685_, 0);
lean_inc(v_canonExpr_692_);
lean_dec_ref(v_inst_685_);
v___x_693_ = l_Lean_mkConst(v___x_686_, v___x_687_);
lean_inc_ref(v_type_688_);
v___x_694_ = l_Lean_mkApp4(v___x_693_, v_type_688_, v___x_689_, v_type_688_, v_inst_690_);
v___x_695_ = lean_apply_1(v_canonExpr_692_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(lean_object* v___x_705_, lean_object* v_type_706_, lean_object* v_semiringInst_707_, lean_object* v___x_708_, lean_object* v_inst_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v_inst_712_, lean_object* v_toBind_713_, lean_object* v_inst_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_inst_x27_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___f_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_715_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__3));
v___x_716_ = l_Lean_mkConst(v___x_715_, v___x_705_);
lean_inc_ref(v_type_706_);
v_inst_x27_717_ = l_Lean_mkAppB(v___x_716_, v_type_706_, v_semiringInst_707_);
v___x_718_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4));
v___x_719_ = l_Lean_Name_mkStr2(v___x_708_, v___x_718_);
lean_inc_ref(v_inst_714_);
lean_inc(v___x_719_);
v___f_720_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_720_, 0, v_inst_709_);
lean_closure_set(v___f_720_, 1, v___x_719_);
lean_closure_set(v___f_720_, 2, v___x_710_);
lean_closure_set(v___f_720_, 3, v_type_706_);
lean_closure_set(v___f_720_, 4, v___x_711_);
lean_closure_set(v___f_720_, 5, v_inst_714_);
v___x_721_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_721_, 0, v___x_719_);
lean_closure_set(v___x_721_, 1, v_inst_714_);
lean_closure_set(v___x_721_, 2, v_inst_x27_717_);
v___x_722_ = lean_apply_2(v_inst_712_, lean_box(0), v___x_721_);
v___x_723_ = lean_apply_4(v_toBind_713_, lean_box(0), lean_box(0), v___x_722_, v___f_720_);
return v___x_723_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = l_Lean_Level_ofNat(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_u_733_, lean_object* v_type_734_, lean_object* v_semiringInst_735_){
_start:
{
lean_object* v_toBind_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_toBind_736_ = lean_ctor_get(v_inst_731_, 1);
lean_inc_n(v_toBind_736_, 2);
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0));
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1));
v___x_739_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_740_ = lean_box(0);
lean_inc(v_u_733_);
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v_u_733_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
lean_inc_ref(v___x_741_);
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_739_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v_u_733_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_inc_ref(v___x_743_);
v___x_744_ = l_Lean_mkConst(v___x_738_, v___x_743_);
v___x_745_ = l_Lean_Nat_mkType;
lean_inc_ref(v_inst_732_);
lean_inc_ref_n(v_type_734_, 2);
v___f_746_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1), 10, 9);
lean_closure_set(v___f_746_, 0, v___x_741_);
lean_closure_set(v___f_746_, 1, v_type_734_);
lean_closure_set(v___f_746_, 2, v_semiringInst_735_);
lean_closure_set(v___f_746_, 3, v___x_737_);
lean_closure_set(v___f_746_, 4, v_inst_732_);
lean_closure_set(v___f_746_, 5, v___x_743_);
lean_closure_set(v___f_746_, 6, v___x_745_);
lean_closure_set(v___f_746_, 7, v_inst_729_);
lean_closure_set(v___f_746_, 8, v_toBind_736_);
v___x_747_ = l_Lean_mkApp3(v___x_744_, v_type_734_, v___x_745_, v_type_734_);
v___x_748_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_731_, v_inst_730_, v_inst_732_, v___x_747_);
v___x_749_ = lean_apply_4(v_toBind_736_, lean_box(0), lean_box(0), v___x_748_, v___f_746_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(lean_object* v_m_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_u_755_, lean_object* v_type_756_, lean_object* v_semiringInst_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_751_, v_inst_752_, v_inst_753_, v_inst_754_, v_u_755_, v_type_756_, v_semiringInst_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0(lean_object* v___x_759_, lean_object* v___x_760_, lean_object* v___x_761_, lean_object* v_type_762_, lean_object* v_canonExpr_763_, lean_object* v_inst_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_765_ = l_Lean_Name_mkStr2(v___x_759_, v___x_760_);
v___x_766_ = l_Lean_mkConst(v___x_765_, v___x_761_);
v___x_767_ = l_Lean_mkAppB(v___x_766_, v_type_762_, v_inst_764_);
v___x_768_ = lean_apply_1(v_canonExpr_763_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(lean_object* v___f_769_, lean_object* v_inst_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = lean_apply_1(v___f_769_, v_inst_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(lean_object* v_toPure_772_, lean_object* v_val_773_, lean_object* v_toBind_774_, lean_object* v___f_775_, lean_object* v_____r_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_apply_2(v_toPure_772_, lean_box(0), v_val_773_);
v___x_778_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_777_, v___f_775_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(lean_object* v_toPure_779_, lean_object* v_inst_x27_780_, lean_object* v_toBind_781_, lean_object* v___f_782_, lean_object* v___f_783_, lean_object* v___x_784_, lean_object* v___x_785_, lean_object* v_inst_786_, lean_object* v_____do__lift_787_){
_start:
{
if (lean_obj_tag(v_____do__lift_787_) == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec(v_inst_786_);
lean_dec_ref(v___x_785_);
lean_dec_ref(v___x_784_);
lean_dec(v___f_783_);
v___x_788_ = lean_apply_2(v_toPure_779_, lean_box(0), v_inst_x27_780_);
v___x_789_ = lean_apply_4(v_toBind_781_, lean_box(0), lean_box(0), v___x_788_, v___f_782_);
return v___x_789_;
}
else
{
lean_object* v_val_790_; lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v___f_782_);
v_val_790_ = lean_ctor_get(v_____do__lift_787_, 0);
lean_inc_n(v_val_790_, 2);
lean_dec_ref_known(v_____do__lift_787_, 1);
lean_inc(v_toBind_781_);
v___f_791_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_791_, 0, v_toPure_779_);
lean_closure_set(v___f_791_, 1, v_val_790_);
lean_closure_set(v___f_791_, 2, v_toBind_781_);
lean_closure_set(v___f_791_, 3, v___f_783_);
v___x_792_ = l_Lean_Name_mkStr2(v___x_784_, v___x_785_);
v___x_793_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_793_, 0, v___x_792_);
lean_closure_set(v___x_793_, 1, v_val_790_);
lean_closure_set(v___x_793_, 2, v_inst_x27_780_);
v___x_794_ = lean_apply_2(v_inst_786_, lean_box(0), v___x_793_);
v___x_795_ = lean_apply_4(v_toBind_781_, lean_box(0), lean_box(0), v___x_794_, v___f_791_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_u_808_, lean_object* v_type_809_, lean_object* v_semiringInst_810_){
_start:
{
lean_object* v_toApplicative_811_; lean_object* v_toBind_812_; lean_object* v_canonExpr_813_; lean_object* v_synthInstance_x3f_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_836_; 
v_toApplicative_811_ = lean_ctor_get(v_inst_806_, 0);
lean_inc_ref(v_toApplicative_811_);
v_toBind_812_ = lean_ctor_get(v_inst_806_, 1);
lean_inc(v_toBind_812_);
lean_dec_ref(v_inst_806_);
v_canonExpr_813_ = lean_ctor_get(v_inst_807_, 0);
v_synthInstance_x3f_814_ = lean_ctor_get(v_inst_807_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_inst_807_);
if (v_isSharedCheck_836_ == 0)
{
v___x_816_ = v_inst_807_;
v_isShared_817_ = v_isSharedCheck_836_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_synthInstance_x3f_814_);
lean_inc(v_canonExpr_813_);
lean_dec(v_inst_807_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_836_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_toPure_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v_toPure_818_ = lean_ctor_get(v_toApplicative_811_, 1);
lean_inc(v_toPure_818_);
lean_dec_ref(v_toApplicative_811_);
v___x_819_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0));
v___x_820_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1));
v___x_821_ = lean_box(0);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 1);
lean_ctor_set(v___x_816_, 1, v___x_821_);
lean_ctor_set(v___x_816_, 0, v_u_808_);
v___x_823_ = v___x_816_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_u_808_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_821_);
v___x_823_ = v_reuseFailAlloc_835_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; lean_object* v_inst_x27_825_; lean_object* v___x_826_; lean_object* v___f_827_; lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_instType_831_; lean_object* v___x_832_; lean_object* v___f_833_; lean_object* v___x_834_; 
lean_inc_ref_n(v___x_823_, 2);
v___x_824_ = l_Lean_mkConst(v___x_820_, v___x_823_);
lean_inc_ref_n(v_type_809_, 2);
v_inst_x27_825_ = l_Lean_mkAppB(v___x_824_, v_type_809_, v_semiringInst_810_);
v___x_826_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2));
v___f_827_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_827_, 0, v___x_826_);
lean_closure_set(v___f_827_, 1, v___x_819_);
lean_closure_set(v___f_827_, 2, v___x_823_);
lean_closure_set(v___f_827_, 3, v_type_809_);
lean_closure_set(v___f_827_, 4, v_canonExpr_813_);
v___f_828_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_828_, 0, v___f_827_);
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3));
v___x_830_ = l_Lean_mkConst(v___x_829_, v___x_823_);
v_instType_831_ = l_Lean_Expr_app___override(v___x_830_, v_type_809_);
v___x_832_ = lean_apply_1(v_synthInstance_x3f_814_, v_instType_831_);
lean_inc_ref(v___f_828_);
lean_inc(v_toBind_812_);
v___f_833_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(v___f_833_, 0, v_toPure_818_);
lean_closure_set(v___f_833_, 1, v_inst_x27_825_);
lean_closure_set(v___f_833_, 2, v_toBind_812_);
lean_closure_set(v___f_833_, 3, v___f_828_);
lean_closure_set(v___f_833_, 4, v___f_828_);
lean_closure_set(v___f_833_, 5, v___x_826_);
lean_closure_set(v___f_833_, 6, v___x_819_);
lean_closure_set(v___f_833_, 7, v_inst_805_);
v___x_834_ = lean_apply_4(v_toBind_812_, lean_box(0), lean_box(0), v___x_832_, v___f_833_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn(lean_object* v_m_837_, lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_u_841_, lean_object* v_type_842_, lean_object* v_semiringInst_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_838_, v_inst_839_, v_inst_840_, v_u_841_, v_type_842_, v_semiringInst_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0(lean_object* v___x_846_, lean_object* v___x_847_, lean_object* v_scalar_848_, lean_object* v_type_849_, lean_object* v_canonExpr_850_, lean_object* v_inst_851_){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_852_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0));
v___x_853_ = l_Lean_Name_mkStr2(v___x_846_, v___x_852_);
v___x_854_ = l_Lean_mkConst(v___x_853_, v___x_847_);
lean_inc_ref(v_type_849_);
v___x_855_ = l_Lean_mkApp4(v___x_854_, v_scalar_848_, v_type_849_, v_type_849_, v_inst_851_);
v___x_856_ = lean_apply_1(v_canonExpr_850_, v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__4(lean_object* v_toPure_857_, lean_object* v_inst_x27_858_, lean_object* v_toBind_859_, lean_object* v___f_860_, lean_object* v___f_861_, lean_object* v___x_862_, lean_object* v_inst_863_, lean_object* v_____do__lift_864_){
_start:
{
if (lean_obj_tag(v_____do__lift_864_) == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec(v_inst_863_);
lean_dec_ref(v___x_862_);
lean_dec(v___f_861_);
v___x_865_ = lean_apply_2(v_toPure_857_, lean_box(0), v_inst_x27_858_);
v___x_866_ = lean_apply_4(v_toBind_859_, lean_box(0), lean_box(0), v___x_865_, v___f_860_);
return v___x_866_;
}
else
{
lean_object* v_val_867_; lean_object* v___f_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v___f_860_);
v_val_867_ = lean_ctor_get(v_____do__lift_864_, 0);
lean_inc_n(v_val_867_, 2);
lean_dec_ref_known(v_____do__lift_864_, 1);
lean_inc(v_toBind_859_);
v___f_868_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_868_, 0, v_toPure_857_);
lean_closure_set(v___f_868_, 1, v_val_867_);
lean_closure_set(v___f_868_, 2, v_toBind_859_);
lean_closure_set(v___f_868_, 3, v___f_861_);
v___x_869_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0___closed__0));
v___x_870_ = l_Lean_Name_mkStr2(v___x_862_, v___x_869_);
v___x_871_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_871_, 0, v___x_870_);
lean_closure_set(v___x_871_, 1, v_val_867_);
lean_closure_set(v___x_871_, 2, v_inst_x27_858_);
v___x_872_ = lean_apply_2(v_inst_863_, lean_box(0), v___x_871_);
v___x_873_ = lean_apply_4(v_toBind_859_, lean_box(0), lean_box(0), v___x_872_, v___f_868_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_u_883_, lean_object* v_type_884_, lean_object* v_scalar_885_, lean_object* v_expectedSMulInst_886_){
_start:
{
lean_object* v_toApplicative_887_; lean_object* v_toBind_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_921_; 
v_toApplicative_887_ = lean_ctor_get(v_inst_881_, 0);
v_toBind_888_ = lean_ctor_get(v_inst_881_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_inst_881_);
if (v_isSharedCheck_921_ == 0)
{
v___x_890_ = v_inst_881_;
v_isShared_891_ = v_isSharedCheck_921_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_toBind_888_);
lean_inc(v_toApplicative_887_);
lean_dec(v_inst_881_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_921_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_canonExpr_892_; lean_object* v_synthInstance_x3f_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_920_; 
v_canonExpr_892_ = lean_ctor_get(v_inst_882_, 0);
v_synthInstance_x3f_893_ = lean_ctor_get(v_inst_882_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_inst_882_);
if (v_isSharedCheck_920_ == 0)
{
v___x_895_ = v_inst_882_;
v_isShared_896_ = v_isSharedCheck_920_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_synthInstance_x3f_893_);
lean_inc(v_canonExpr_892_);
lean_dec(v_inst_882_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_920_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_897_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__1));
v___x_898_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_899_ = lean_box(0);
lean_inc(v_u_883_);
if (v_isShared_896_ == 0)
{
lean_ctor_set_tag(v___x_895_, 1);
lean_ctor_set(v___x_895_, 1, v___x_899_);
lean_ctor_set(v___x_895_, 0, v_u_883_);
v___x_901_ = v___x_895_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_u_883_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_899_);
v___x_901_ = v_reuseFailAlloc_919_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_903_; 
lean_inc_ref(v___x_901_);
if (v_isShared_891_ == 0)
{
lean_ctor_set_tag(v___x_890_, 1);
lean_ctor_set(v___x_890_, 1, v___x_901_);
lean_ctor_set(v___x_890_, 0, v___x_898_);
v___x_903_ = v___x_890_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_918_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v_inst_x27_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_toPure_912_; lean_object* v___f_913_; lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___x_917_; 
v___x_904_ = l_Lean_mkConst(v___x_897_, v___x_903_);
lean_inc_ref_n(v_type_884_, 3);
lean_inc_ref_n(v_scalar_885_, 2);
v_inst_x27_905_ = l_Lean_mkApp3(v___x_904_, v_scalar_885_, v_type_884_, v_expectedSMulInst_886_);
v___x_906_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__2));
v___x_907_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___closed__3));
v___x_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_908_, 0, v_u_883_);
lean_ctor_set(v___x_908_, 1, v___x_901_);
v___x_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_898_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
lean_inc_ref(v___x_909_);
v___x_910_ = l_Lean_mkConst(v___x_907_, v___x_909_);
v___x_911_ = l_Lean_mkApp3(v___x_910_, v_scalar_885_, v_type_884_, v_type_884_);
v_toPure_912_ = lean_ctor_get(v_toApplicative_887_, 1);
lean_inc(v_toPure_912_);
lean_dec_ref(v_toApplicative_887_);
v___f_913_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_913_, 0, v___x_906_);
lean_closure_set(v___f_913_, 1, v___x_909_);
lean_closure_set(v___f_913_, 2, v_scalar_885_);
lean_closure_set(v___f_913_, 3, v_type_884_);
lean_closure_set(v___f_913_, 4, v_canonExpr_892_);
v___f_914_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_914_, 0, v___f_913_);
v___x_915_ = lean_apply_1(v_synthInstance_x3f_893_, v___x_911_);
lean_inc_ref(v___f_914_);
lean_inc(v_toBind_888_);
v___f_916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg___lam__4), 8, 7);
lean_closure_set(v___f_916_, 0, v_toPure_912_);
lean_closure_set(v___f_916_, 1, v_inst_x27_905_);
lean_closure_set(v___f_916_, 2, v_toBind_888_);
lean_closure_set(v___f_916_, 3, v___f_914_);
lean_closure_set(v___f_916_, 4, v___f_914_);
lean_closure_set(v___f_916_, 5, v___x_906_);
lean_closure_set(v___f_916_, 6, v_inst_880_);
v___x_917_ = lean_apply_4(v_toBind_888_, lean_box(0), lean_box(0), v___x_915_, v___f_916_);
return v___x_917_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn(lean_object* v_m_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_u_926_, lean_object* v_type_927_, lean_object* v_scalar_928_, lean_object* v_expectedSMulInst_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_923_, v_inst_924_, v_inst_925_, v_u_926_, v_type_927_, v_scalar_928_, v_expectedSMulInst_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0(lean_object* v_fn_931_, lean_object* v_s_932_){
_start:
{
lean_object* v_id_933_; lean_object* v_type_934_; lean_object* v_u_935_; lean_object* v_ringInst_936_; lean_object* v_semiringInst_937_; lean_object* v_charInst_x3f_938_; uint8_t v_symbolicChar_939_; lean_object* v_addFn_x3f_940_; lean_object* v_mulFn_x3f_941_; lean_object* v_subFn_x3f_942_; lean_object* v_negFn_x3f_943_; lean_object* v_powFn_x3f_944_; lean_object* v_intCastFn_x3f_945_; lean_object* v_natCastFn_x3f_946_; lean_object* v_intSMulFn_x3f_947_; lean_object* v_one_x3f_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_956_; 
v_id_933_ = lean_ctor_get(v_s_932_, 0);
v_type_934_ = lean_ctor_get(v_s_932_, 1);
v_u_935_ = lean_ctor_get(v_s_932_, 2);
v_ringInst_936_ = lean_ctor_get(v_s_932_, 3);
v_semiringInst_937_ = lean_ctor_get(v_s_932_, 4);
v_charInst_x3f_938_ = lean_ctor_get(v_s_932_, 5);
v_symbolicChar_939_ = lean_ctor_get_uint8(v_s_932_, sizeof(void*)*16);
v_addFn_x3f_940_ = lean_ctor_get(v_s_932_, 6);
v_mulFn_x3f_941_ = lean_ctor_get(v_s_932_, 7);
v_subFn_x3f_942_ = lean_ctor_get(v_s_932_, 8);
v_negFn_x3f_943_ = lean_ctor_get(v_s_932_, 9);
v_powFn_x3f_944_ = lean_ctor_get(v_s_932_, 10);
v_intCastFn_x3f_945_ = lean_ctor_get(v_s_932_, 11);
v_natCastFn_x3f_946_ = lean_ctor_get(v_s_932_, 12);
v_intSMulFn_x3f_947_ = lean_ctor_get(v_s_932_, 14);
v_one_x3f_948_ = lean_ctor_get(v_s_932_, 15);
v_isSharedCheck_956_ = !lean_is_exclusive(v_s_932_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v_s_932_, 13);
lean_dec(v_unused_957_);
v___x_950_ = v_s_932_;
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_one_x3f_948_);
lean_inc(v_intSMulFn_x3f_947_);
lean_inc(v_natCastFn_x3f_946_);
lean_inc(v_intCastFn_x3f_945_);
lean_inc(v_powFn_x3f_944_);
lean_inc(v_negFn_x3f_943_);
lean_inc(v_subFn_x3f_942_);
lean_inc(v_mulFn_x3f_941_);
lean_inc(v_addFn_x3f_940_);
lean_inc(v_charInst_x3f_938_);
lean_inc(v_semiringInst_937_);
lean_inc(v_ringInst_936_);
lean_inc(v_u_935_);
lean_inc(v_type_934_);
lean_inc(v_id_933_);
lean_dec(v_s_932_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_952_, 0, v_fn_931_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 13, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_id_933_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_type_934_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_u_935_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_ringInst_936_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_semiringInst_937_);
lean_ctor_set(v_reuseFailAlloc_955_, 5, v_charInst_x3f_938_);
lean_ctor_set(v_reuseFailAlloc_955_, 6, v_addFn_x3f_940_);
lean_ctor_set(v_reuseFailAlloc_955_, 7, v_mulFn_x3f_941_);
lean_ctor_set(v_reuseFailAlloc_955_, 8, v_subFn_x3f_942_);
lean_ctor_set(v_reuseFailAlloc_955_, 9, v_negFn_x3f_943_);
lean_ctor_set(v_reuseFailAlloc_955_, 10, v_powFn_x3f_944_);
lean_ctor_set(v_reuseFailAlloc_955_, 11, v_intCastFn_x3f_945_);
lean_ctor_set(v_reuseFailAlloc_955_, 12, v_natCastFn_x3f_946_);
lean_ctor_set(v_reuseFailAlloc_955_, 13, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_955_, 14, v_intSMulFn_x3f_947_);
lean_ctor_set(v_reuseFailAlloc_955_, 15, v_one_x3f_948_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, sizeof(void*)*16, v_symbolicChar_939_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1(lean_object* v_toPure_958_, lean_object* v_fn_959_, lean_object* v_____r_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = lean_apply_2(v_toPure_958_, lean_box(0), v_fn_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2(lean_object* v_toPure_962_, lean_object* v_modifyRing_963_, lean_object* v_toBind_964_, lean_object* v_fn_965_){
_start:
{
lean_object* v___f_966_; lean_object* v___f_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_inc_ref(v_fn_965_);
v___f_966_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_966_, 0, v_fn_965_);
v___f_967_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_967_, 0, v_toPure_962_);
lean_closure_set(v___f_967_, 1, v_fn_965_);
v___x_968_ = lean_apply_1(v_modifyRing_963_, v___f_966_);
v___x_969_ = lean_apply_4(v_toBind_964_, lean_box(0), lean_box(0), v___x_968_, v___f_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3(lean_object* v_toPure_976_, lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_toBind_980_, lean_object* v___f_981_, lean_object* v_ring_982_){
_start:
{
lean_object* v_natSMulFn_x3f_983_; 
v_natSMulFn_x3f_983_ = lean_ctor_get(v_ring_982_, 13);
if (lean_obj_tag(v_natSMulFn_x3f_983_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_985_; 
lean_inc_ref(v_natSMulFn_x3f_983_);
lean_dec_ref(v_ring_982_);
lean_dec(v___f_981_);
lean_dec(v_toBind_980_);
lean_dec_ref(v_inst_979_);
lean_dec_ref(v_inst_978_);
lean_dec(v_inst_977_);
v_val_984_ = lean_ctor_get(v_natSMulFn_x3f_983_, 0);
lean_inc(v_val_984_);
lean_dec_ref_known(v_natSMulFn_x3f_983_, 1);
v___x_985_ = lean_apply_2(v_toPure_976_, lean_box(0), v_val_984_);
return v___x_985_;
}
else
{
lean_object* v_type_986_; lean_object* v_u_987_; lean_object* v_semiringInst_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec(v_toPure_976_);
v_type_986_ = lean_ctor_get(v_ring_982_, 1);
lean_inc_ref_n(v_type_986_, 2);
v_u_987_ = lean_ctor_get(v_ring_982_, 2);
lean_inc_n(v_u_987_, 2);
v_semiringInst_988_ = lean_ctor_get(v_ring_982_, 4);
lean_inc_ref(v_semiringInst_988_);
lean_dec_ref(v_ring_982_);
v___x_989_ = l_Lean_Nat_mkType;
v___x_990_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1));
v___x_991_ = lean_box(0);
v___x_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_992_, 0, v_u_987_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_mkConst(v___x_990_, v___x_992_);
v___x_994_ = l_Lean_mkAppB(v___x_993_, v_type_986_, v_semiringInst_988_);
v___x_995_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_977_, v_inst_978_, v_inst_979_, v_u_987_, v_type_986_, v___x_989_, v___x_994_);
v___x_996_ = lean_apply_4(v_toBind_980_, lean_box(0), lean_box(0), v___x_995_, v___f_981_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_inst_1000_){
_start:
{
lean_object* v_toApplicative_1001_; lean_object* v_toBind_1002_; lean_object* v_getRing_1003_; lean_object* v_modifyRing_1004_; lean_object* v_toPure_1005_; lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; 
v_toApplicative_1001_ = lean_ctor_get(v_inst_998_, 0);
v_toBind_1002_ = lean_ctor_get(v_inst_998_, 1);
lean_inc_n(v_toBind_1002_, 3);
v_getRing_1003_ = lean_ctor_get(v_inst_1000_, 0);
lean_inc(v_getRing_1003_);
v_modifyRing_1004_ = lean_ctor_get(v_inst_1000_, 1);
lean_inc(v_modifyRing_1004_);
lean_dec_ref(v_inst_1000_);
v_toPure_1005_ = lean_ctor_get(v_toApplicative_1001_, 1);
lean_inc_n(v_toPure_1005_, 2);
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1006_, 0, v_toPure_1005_);
lean_closure_set(v___f_1006_, 1, v_modifyRing_1004_);
lean_closure_set(v___f_1006_, 2, v_toBind_1002_);
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1007_, 0, v_toPure_1005_);
lean_closure_set(v___f_1007_, 1, v_inst_997_);
lean_closure_set(v___f_1007_, 2, v_inst_998_);
lean_closure_set(v___f_1007_, 3, v_inst_999_);
lean_closure_set(v___f_1007_, 4, v_toBind_1002_);
lean_closure_set(v___f_1007_, 5, v___f_1006_);
v___x_1008_ = lean_apply_4(v_toBind_1002_, lean_box(0), lean_box(0), v_getRing_1003_, v___f_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn(lean_object* v_m_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg(v_inst_1010_, v_inst_1011_, v_inst_1012_, v_inst_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0(lean_object* v_fn_1015_, lean_object* v_s_1016_){
_start:
{
lean_object* v_id_1017_; lean_object* v_type_1018_; lean_object* v_u_1019_; lean_object* v_ringInst_1020_; lean_object* v_semiringInst_1021_; lean_object* v_charInst_x3f_1022_; uint8_t v_symbolicChar_1023_; lean_object* v_addFn_x3f_1024_; lean_object* v_mulFn_x3f_1025_; lean_object* v_subFn_x3f_1026_; lean_object* v_negFn_x3f_1027_; lean_object* v_powFn_x3f_1028_; lean_object* v_intCastFn_x3f_1029_; lean_object* v_natCastFn_x3f_1030_; lean_object* v_natSMulFn_x3f_1031_; lean_object* v_one_x3f_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_id_1017_ = lean_ctor_get(v_s_1016_, 0);
v_type_1018_ = lean_ctor_get(v_s_1016_, 1);
v_u_1019_ = lean_ctor_get(v_s_1016_, 2);
v_ringInst_1020_ = lean_ctor_get(v_s_1016_, 3);
v_semiringInst_1021_ = lean_ctor_get(v_s_1016_, 4);
v_charInst_x3f_1022_ = lean_ctor_get(v_s_1016_, 5);
v_symbolicChar_1023_ = lean_ctor_get_uint8(v_s_1016_, sizeof(void*)*16);
v_addFn_x3f_1024_ = lean_ctor_get(v_s_1016_, 6);
v_mulFn_x3f_1025_ = lean_ctor_get(v_s_1016_, 7);
v_subFn_x3f_1026_ = lean_ctor_get(v_s_1016_, 8);
v_negFn_x3f_1027_ = lean_ctor_get(v_s_1016_, 9);
v_powFn_x3f_1028_ = lean_ctor_get(v_s_1016_, 10);
v_intCastFn_x3f_1029_ = lean_ctor_get(v_s_1016_, 11);
v_natCastFn_x3f_1030_ = lean_ctor_get(v_s_1016_, 12);
v_natSMulFn_x3f_1031_ = lean_ctor_get(v_s_1016_, 13);
v_one_x3f_1032_ = lean_ctor_get(v_s_1016_, 15);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_s_1016_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_s_1016_, 14);
lean_dec(v_unused_1041_);
v___x_1034_ = v_s_1016_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_one_x3f_1032_);
lean_inc(v_natSMulFn_x3f_1031_);
lean_inc(v_natCastFn_x3f_1030_);
lean_inc(v_intCastFn_x3f_1029_);
lean_inc(v_powFn_x3f_1028_);
lean_inc(v_negFn_x3f_1027_);
lean_inc(v_subFn_x3f_1026_);
lean_inc(v_mulFn_x3f_1025_);
lean_inc(v_addFn_x3f_1024_);
lean_inc(v_charInst_x3f_1022_);
lean_inc(v_semiringInst_1021_);
lean_inc(v_ringInst_1020_);
lean_inc(v_u_1019_);
lean_inc(v_type_1018_);
lean_inc(v_id_1017_);
lean_dec(v_s_1016_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_fn_1015_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 14, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_id_1017_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_type_1018_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_u_1019_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_ringInst_1020_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_semiringInst_1021_);
lean_ctor_set(v_reuseFailAlloc_1039_, 5, v_charInst_x3f_1022_);
lean_ctor_set(v_reuseFailAlloc_1039_, 6, v_addFn_x3f_1024_);
lean_ctor_set(v_reuseFailAlloc_1039_, 7, v_mulFn_x3f_1025_);
lean_ctor_set(v_reuseFailAlloc_1039_, 8, v_subFn_x3f_1026_);
lean_ctor_set(v_reuseFailAlloc_1039_, 9, v_negFn_x3f_1027_);
lean_ctor_set(v_reuseFailAlloc_1039_, 10, v_powFn_x3f_1028_);
lean_ctor_set(v_reuseFailAlloc_1039_, 11, v_intCastFn_x3f_1029_);
lean_ctor_set(v_reuseFailAlloc_1039_, 12, v_natCastFn_x3f_1030_);
lean_ctor_set(v_reuseFailAlloc_1039_, 13, v_natSMulFn_x3f_1031_);
lean_ctor_set(v_reuseFailAlloc_1039_, 14, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 15, v_one_x3f_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1039_, sizeof(void*)*16, v_symbolicChar_1023_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2(lean_object* v_toPure_1042_, lean_object* v_modifyRing_1043_, lean_object* v_toBind_1044_, lean_object* v_fn_1045_){
_start:
{
lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_inc_ref(v_fn_1045_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1046_, 0, v_fn_1045_);
v___f_1047_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1047_, 0, v_toPure_1042_);
lean_closure_set(v___f_1047_, 1, v_fn_1045_);
v___x_1048_ = lean_apply_1(v_modifyRing_1043_, v___f_1046_);
v___x_1049_ = lean_apply_4(v_toBind_1044_, lean_box(0), lean_box(0), v___x_1048_, v___f_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1(lean_object* v_toPure_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_toBind_1061_, lean_object* v___f_1062_, lean_object* v_ring_1063_){
_start:
{
lean_object* v_intSMulFn_x3f_1064_; 
v_intSMulFn_x3f_1064_ = lean_ctor_get(v_ring_1063_, 14);
if (lean_obj_tag(v_intSMulFn_x3f_1064_) == 1)
{
lean_object* v_val_1065_; lean_object* v___x_1066_; 
lean_inc_ref(v_intSMulFn_x3f_1064_);
lean_dec_ref(v_ring_1063_);
lean_dec(v___f_1062_);
lean_dec(v_toBind_1061_);
lean_dec_ref(v_inst_1060_);
lean_dec_ref(v_inst_1059_);
lean_dec(v_inst_1058_);
v_val_1065_ = lean_ctor_get(v_intSMulFn_x3f_1064_, 0);
lean_inc(v_val_1065_);
lean_dec_ref_known(v_intSMulFn_x3f_1064_, 1);
v___x_1066_ = lean_apply_2(v_toPure_1057_, lean_box(0), v_val_1065_);
return v___x_1066_;
}
else
{
lean_object* v_type_1067_; lean_object* v_u_1068_; lean_object* v_ringInst_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v_toPure_1057_);
v_type_1067_ = lean_ctor_get(v_ring_1063_, 1);
lean_inc_ref_n(v_type_1067_, 2);
v_u_1068_ = lean_ctor_get(v_ring_1063_, 2);
lean_inc_n(v_u_1068_, 2);
v_ringInst_1069_ = lean_ctor_get(v_ring_1063_, 3);
lean_inc_ref(v_ringInst_1069_);
lean_dec_ref(v_ring_1063_);
v___x_1070_ = l_Lean_Int_mkType;
v___x_1071_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1___closed__2));
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_u_1068_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l_Lean_mkConst(v___x_1071_, v___x_1073_);
v___x_1075_ = l_Lean_mkAppB(v___x_1074_, v_type_1067_, v_ringInst_1069_);
v___x_1076_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_1058_, v_inst_1059_, v_inst_1060_, v_u_1068_, v_type_1067_, v___x_1070_, v___x_1075_);
v___x_1077_ = lean_apply_4(v_toBind_1061_, lean_box(0), lean_box(0), v___x_1076_, v___f_1062_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_){
_start:
{
lean_object* v_toApplicative_1082_; lean_object* v_toBind_1083_; lean_object* v_getRing_1084_; lean_object* v_modifyRing_1085_; lean_object* v_toPure_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; 
v_toApplicative_1082_ = lean_ctor_get(v_inst_1079_, 0);
v_toBind_1083_ = lean_ctor_get(v_inst_1079_, 1);
lean_inc_n(v_toBind_1083_, 3);
v_getRing_1084_ = lean_ctor_get(v_inst_1081_, 0);
lean_inc(v_getRing_1084_);
v_modifyRing_1085_ = lean_ctor_get(v_inst_1081_, 1);
lean_inc(v_modifyRing_1085_);
lean_dec_ref(v_inst_1081_);
v_toPure_1086_ = lean_ctor_get(v_toApplicative_1082_, 1);
lean_inc_n(v_toPure_1086_, 2);
v___f_1087_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1087_, 0, v_toPure_1086_);
lean_closure_set(v___f_1087_, 1, v_modifyRing_1085_);
lean_closure_set(v___f_1087_, 2, v_toBind_1083_);
v___f_1088_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1088_, 0, v_toPure_1086_);
lean_closure_set(v___f_1088_, 1, v_inst_1078_);
lean_closure_set(v___f_1088_, 2, v_inst_1079_);
lean_closure_set(v___f_1088_, 3, v_inst_1080_);
lean_closure_set(v___f_1088_, 4, v_toBind_1083_);
lean_closure_set(v___f_1088_, 5, v___f_1087_);
v___x_1089_ = lean_apply_4(v_toBind_1083_, lean_box(0), lean_box(0), v_getRing_1084_, v___f_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntSMulFn(lean_object* v_m_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Meta_Sym_Arith_getIntSMulFn___redArg(v_inst_1091_, v_inst_1092_, v_inst_1093_, v_inst_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object* v_addFn_1096_, lean_object* v_s_1097_){
_start:
{
lean_object* v_id_1098_; lean_object* v_type_1099_; lean_object* v_u_1100_; lean_object* v_ringInst_1101_; lean_object* v_semiringInst_1102_; lean_object* v_charInst_x3f_1103_; uint8_t v_symbolicChar_1104_; lean_object* v_mulFn_x3f_1105_; lean_object* v_subFn_x3f_1106_; lean_object* v_negFn_x3f_1107_; lean_object* v_powFn_x3f_1108_; lean_object* v_intCastFn_x3f_1109_; lean_object* v_natCastFn_x3f_1110_; lean_object* v_natSMulFn_x3f_1111_; lean_object* v_intSMulFn_x3f_1112_; lean_object* v_one_x3f_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
v_id_1098_ = lean_ctor_get(v_s_1097_, 0);
v_type_1099_ = lean_ctor_get(v_s_1097_, 1);
v_u_1100_ = lean_ctor_get(v_s_1097_, 2);
v_ringInst_1101_ = lean_ctor_get(v_s_1097_, 3);
v_semiringInst_1102_ = lean_ctor_get(v_s_1097_, 4);
v_charInst_x3f_1103_ = lean_ctor_get(v_s_1097_, 5);
v_symbolicChar_1104_ = lean_ctor_get_uint8(v_s_1097_, sizeof(void*)*16);
v_mulFn_x3f_1105_ = lean_ctor_get(v_s_1097_, 7);
v_subFn_x3f_1106_ = lean_ctor_get(v_s_1097_, 8);
v_negFn_x3f_1107_ = lean_ctor_get(v_s_1097_, 9);
v_powFn_x3f_1108_ = lean_ctor_get(v_s_1097_, 10);
v_intCastFn_x3f_1109_ = lean_ctor_get(v_s_1097_, 11);
v_natCastFn_x3f_1110_ = lean_ctor_get(v_s_1097_, 12);
v_natSMulFn_x3f_1111_ = lean_ctor_get(v_s_1097_, 13);
v_intSMulFn_x3f_1112_ = lean_ctor_get(v_s_1097_, 14);
v_one_x3f_1113_ = lean_ctor_get(v_s_1097_, 15);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_s_1097_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_s_1097_, 6);
lean_dec(v_unused_1122_);
v___x_1115_ = v_s_1097_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_one_x3f_1113_);
lean_inc(v_intSMulFn_x3f_1112_);
lean_inc(v_natSMulFn_x3f_1111_);
lean_inc(v_natCastFn_x3f_1110_);
lean_inc(v_intCastFn_x3f_1109_);
lean_inc(v_powFn_x3f_1108_);
lean_inc(v_negFn_x3f_1107_);
lean_inc(v_subFn_x3f_1106_);
lean_inc(v_mulFn_x3f_1105_);
lean_inc(v_charInst_x3f_1103_);
lean_inc(v_semiringInst_1102_);
lean_inc(v_ringInst_1101_);
lean_inc(v_u_1100_);
lean_inc(v_type_1099_);
lean_inc(v_id_1098_);
lean_dec(v_s_1097_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_addFn_1096_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 6, v___x_1117_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_id_1098_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_type_1099_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_u_1100_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_ringInst_1101_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_semiringInst_1102_);
lean_ctor_set(v_reuseFailAlloc_1120_, 5, v_charInst_x3f_1103_);
lean_ctor_set(v_reuseFailAlloc_1120_, 6, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1120_, 7, v_mulFn_x3f_1105_);
lean_ctor_set(v_reuseFailAlloc_1120_, 8, v_subFn_x3f_1106_);
lean_ctor_set(v_reuseFailAlloc_1120_, 9, v_negFn_x3f_1107_);
lean_ctor_set(v_reuseFailAlloc_1120_, 10, v_powFn_x3f_1108_);
lean_ctor_set(v_reuseFailAlloc_1120_, 11, v_intCastFn_x3f_1109_);
lean_ctor_set(v_reuseFailAlloc_1120_, 12, v_natCastFn_x3f_1110_);
lean_ctor_set(v_reuseFailAlloc_1120_, 13, v_natSMulFn_x3f_1111_);
lean_ctor_set(v_reuseFailAlloc_1120_, 14, v_intSMulFn_x3f_1112_);
lean_ctor_set(v_reuseFailAlloc_1120_, 15, v_one_x3f_1113_);
lean_ctor_set_uint8(v_reuseFailAlloc_1120_, sizeof(void*)*16, v_symbolicChar_1104_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object* v_toPure_1123_, lean_object* v_addFn_1124_, lean_object* v_____r_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_apply_2(v_toPure_1123_, lean_box(0), v_addFn_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object* v_toPure_1127_, lean_object* v_modifyRing_1128_, lean_object* v_toBind_1129_, lean_object* v_addFn_1130_){
_start:
{
lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_inc_ref(v_addFn_1130_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1131_, 0, v_addFn_1130_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1132_, 0, v_toPure_1127_);
lean_closure_set(v___f_1132_, 1, v_addFn_1130_);
v___x_1133_ = lean_apply_1(v_modifyRing_1128_, v___f_1131_);
v___x_1134_ = lean_apply_4(v_toBind_1129_, lean_box(0), lean_box(0), v___x_1133_, v___f_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object* v_toPure_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_toBind_1156_, lean_object* v___f_1157_, lean_object* v_ring_1158_){
_start:
{
lean_object* v_addFn_x3f_1159_; 
v_addFn_x3f_1159_ = lean_ctor_get(v_ring_1158_, 6);
if (lean_obj_tag(v_addFn_x3f_1159_) == 1)
{
lean_object* v_val_1160_; lean_object* v___x_1161_; 
lean_inc_ref(v_addFn_x3f_1159_);
lean_dec_ref(v_ring_1158_);
lean_dec(v___f_1157_);
lean_dec(v_toBind_1156_);
lean_dec_ref(v_inst_1155_);
lean_dec_ref(v_inst_1154_);
lean_dec_ref(v_inst_1153_);
lean_dec(v_inst_1152_);
v_val_1160_ = lean_ctor_get(v_addFn_x3f_1159_, 0);
lean_inc(v_val_1160_);
lean_dec_ref_known(v_addFn_x3f_1159_, 1);
v___x_1161_ = lean_apply_2(v_toPure_1151_, lean_box(0), v_val_1160_);
return v___x_1161_;
}
else
{
lean_object* v_type_1162_; lean_object* v_u_1163_; lean_object* v_semiringInst_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_expectedInst_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v_toPure_1151_);
v_type_1162_ = lean_ctor_get(v_ring_1158_, 1);
lean_inc_ref_n(v_type_1162_, 3);
v_u_1163_ = lean_ctor_get(v_ring_1158_, 2);
lean_inc_n(v_u_1163_, 2);
v_semiringInst_1164_ = lean_ctor_get(v_ring_1158_, 4);
lean_inc_ref(v_semiringInst_1164_);
lean_dec_ref(v_ring_1158_);
v___x_1165_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_u_1163_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
lean_inc_ref(v___x_1167_);
v___x_1168_ = l_Lean_mkConst(v___x_1165_, v___x_1167_);
v___x_1169_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_1170_ = l_Lean_mkConst(v___x_1169_, v___x_1167_);
v___x_1171_ = l_Lean_mkAppB(v___x_1170_, v_type_1162_, v_semiringInst_1164_);
v_expectedInst_1172_ = l_Lean_mkAppB(v___x_1168_, v_type_1162_, v___x_1171_);
v___x_1173_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_1174_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_1175_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1152_, v_inst_1153_, v_inst_1154_, v_inst_1155_, v_type_1162_, v_u_1163_, v___x_1173_, v___x_1174_, v_expectedInst_1172_);
v___x_1176_ = lean_apply_4(v_toBind_1156_, lean_box(0), lean_box(0), v___x_1175_, v___f_1157_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_){
_start:
{
lean_object* v_toApplicative_1182_; lean_object* v_toBind_1183_; lean_object* v_getRing_1184_; lean_object* v_modifyRing_1185_; lean_object* v_toPure_1186_; lean_object* v___f_1187_; lean_object* v___f_1188_; lean_object* v___x_1189_; 
v_toApplicative_1182_ = lean_ctor_get(v_inst_1179_, 0);
v_toBind_1183_ = lean_ctor_get(v_inst_1179_, 1);
lean_inc_n(v_toBind_1183_, 3);
v_getRing_1184_ = lean_ctor_get(v_inst_1181_, 0);
lean_inc(v_getRing_1184_);
v_modifyRing_1185_ = lean_ctor_get(v_inst_1181_, 1);
lean_inc(v_modifyRing_1185_);
lean_dec_ref(v_inst_1181_);
v_toPure_1186_ = lean_ctor_get(v_toApplicative_1182_, 1);
lean_inc_n(v_toPure_1186_, 2);
v___f_1187_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1187_, 0, v_toPure_1186_);
lean_closure_set(v___f_1187_, 1, v_modifyRing_1185_);
lean_closure_set(v___f_1187_, 2, v_toBind_1183_);
v___f_1188_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1188_, 0, v_toPure_1186_);
lean_closure_set(v___f_1188_, 1, v_inst_1177_);
lean_closure_set(v___f_1188_, 2, v_inst_1178_);
lean_closure_set(v___f_1188_, 3, v_inst_1179_);
lean_closure_set(v___f_1188_, 4, v_inst_1180_);
lean_closure_set(v___f_1188_, 5, v_toBind_1183_);
lean_closure_set(v___f_1188_, 6, v___f_1187_);
v___x_1189_ = lean_apply_4(v_toBind_1183_, lean_box(0), lean_box(0), v_getRing_1184_, v___f_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object* v_m_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_1191_, v_inst_1192_, v_inst_1193_, v_inst_1194_, v_inst_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object* v_mulFn_1197_, lean_object* v_s_1198_){
_start:
{
lean_object* v_id_1199_; lean_object* v_type_1200_; lean_object* v_u_1201_; lean_object* v_ringInst_1202_; lean_object* v_semiringInst_1203_; lean_object* v_charInst_x3f_1204_; uint8_t v_symbolicChar_1205_; lean_object* v_addFn_x3f_1206_; lean_object* v_subFn_x3f_1207_; lean_object* v_negFn_x3f_1208_; lean_object* v_powFn_x3f_1209_; lean_object* v_intCastFn_x3f_1210_; lean_object* v_natCastFn_x3f_1211_; lean_object* v_natSMulFn_x3f_1212_; lean_object* v_intSMulFn_x3f_1213_; lean_object* v_one_x3f_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
v_id_1199_ = lean_ctor_get(v_s_1198_, 0);
v_type_1200_ = lean_ctor_get(v_s_1198_, 1);
v_u_1201_ = lean_ctor_get(v_s_1198_, 2);
v_ringInst_1202_ = lean_ctor_get(v_s_1198_, 3);
v_semiringInst_1203_ = lean_ctor_get(v_s_1198_, 4);
v_charInst_x3f_1204_ = lean_ctor_get(v_s_1198_, 5);
v_symbolicChar_1205_ = lean_ctor_get_uint8(v_s_1198_, sizeof(void*)*16);
v_addFn_x3f_1206_ = lean_ctor_get(v_s_1198_, 6);
v_subFn_x3f_1207_ = lean_ctor_get(v_s_1198_, 8);
v_negFn_x3f_1208_ = lean_ctor_get(v_s_1198_, 9);
v_powFn_x3f_1209_ = lean_ctor_get(v_s_1198_, 10);
v_intCastFn_x3f_1210_ = lean_ctor_get(v_s_1198_, 11);
v_natCastFn_x3f_1211_ = lean_ctor_get(v_s_1198_, 12);
v_natSMulFn_x3f_1212_ = lean_ctor_get(v_s_1198_, 13);
v_intSMulFn_x3f_1213_ = lean_ctor_get(v_s_1198_, 14);
v_one_x3f_1214_ = lean_ctor_get(v_s_1198_, 15);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_s_1198_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_s_1198_, 7);
lean_dec(v_unused_1223_);
v___x_1216_ = v_s_1198_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_one_x3f_1214_);
lean_inc(v_intSMulFn_x3f_1213_);
lean_inc(v_natSMulFn_x3f_1212_);
lean_inc(v_natCastFn_x3f_1211_);
lean_inc(v_intCastFn_x3f_1210_);
lean_inc(v_powFn_x3f_1209_);
lean_inc(v_negFn_x3f_1208_);
lean_inc(v_subFn_x3f_1207_);
lean_inc(v_addFn_x3f_1206_);
lean_inc(v_charInst_x3f_1204_);
lean_inc(v_semiringInst_1203_);
lean_inc(v_ringInst_1202_);
lean_inc(v_u_1201_);
lean_inc(v_type_1200_);
lean_inc(v_id_1199_);
lean_dec(v_s_1198_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_mulFn_1197_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 7, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_id_1199_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_type_1200_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_u_1201_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_ringInst_1202_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v_semiringInst_1203_);
lean_ctor_set(v_reuseFailAlloc_1221_, 5, v_charInst_x3f_1204_);
lean_ctor_set(v_reuseFailAlloc_1221_, 6, v_addFn_x3f_1206_);
lean_ctor_set(v_reuseFailAlloc_1221_, 7, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1221_, 8, v_subFn_x3f_1207_);
lean_ctor_set(v_reuseFailAlloc_1221_, 9, v_negFn_x3f_1208_);
lean_ctor_set(v_reuseFailAlloc_1221_, 10, v_powFn_x3f_1209_);
lean_ctor_set(v_reuseFailAlloc_1221_, 11, v_intCastFn_x3f_1210_);
lean_ctor_set(v_reuseFailAlloc_1221_, 12, v_natCastFn_x3f_1211_);
lean_ctor_set(v_reuseFailAlloc_1221_, 13, v_natSMulFn_x3f_1212_);
lean_ctor_set(v_reuseFailAlloc_1221_, 14, v_intSMulFn_x3f_1213_);
lean_ctor_set(v_reuseFailAlloc_1221_, 15, v_one_x3f_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1221_, sizeof(void*)*16, v_symbolicChar_1205_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(lean_object* v_toPure_1224_, lean_object* v_mulFn_1225_, lean_object* v_____r_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_apply_2(v_toPure_1224_, lean_box(0), v_mulFn_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(lean_object* v_toPure_1228_, lean_object* v_modifyRing_1229_, lean_object* v_toBind_1230_, lean_object* v_mulFn_1231_){
_start:
{
lean_object* v___f_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_inc_ref(v_mulFn_1231_);
v___f_1232_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1232_, 0, v_mulFn_1231_);
v___f_1233_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1233_, 0, v_toPure_1228_);
lean_closure_set(v___f_1233_, 1, v_mulFn_1231_);
v___x_1234_ = lean_apply_1(v_modifyRing_1229_, v___f_1232_);
v___x_1235_ = lean_apply_4(v_toBind_1230_, lean_box(0), lean_box(0), v___x_1234_, v___f_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(lean_object* v_toPure_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_toBind_1257_, lean_object* v___f_1258_, lean_object* v_ring_1259_){
_start:
{
lean_object* v_mulFn_x3f_1260_; 
v_mulFn_x3f_1260_ = lean_ctor_get(v_ring_1259_, 7);
if (lean_obj_tag(v_mulFn_x3f_1260_) == 1)
{
lean_object* v_val_1261_; lean_object* v___x_1262_; 
lean_inc_ref(v_mulFn_x3f_1260_);
lean_dec_ref(v_ring_1259_);
lean_dec(v___f_1258_);
lean_dec(v_toBind_1257_);
lean_dec_ref(v_inst_1256_);
lean_dec_ref(v_inst_1255_);
lean_dec_ref(v_inst_1254_);
lean_dec(v_inst_1253_);
v_val_1261_ = lean_ctor_get(v_mulFn_x3f_1260_, 0);
lean_inc(v_val_1261_);
lean_dec_ref_known(v_mulFn_x3f_1260_, 1);
v___x_1262_ = lean_apply_2(v_toPure_1252_, lean_box(0), v_val_1261_);
return v___x_1262_;
}
else
{
lean_object* v_type_1263_; lean_object* v_u_1264_; lean_object* v_semiringInst_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_expectedInst_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_dec(v_toPure_1252_);
v_type_1263_ = lean_ctor_get(v_ring_1259_, 1);
lean_inc_ref_n(v_type_1263_, 3);
v_u_1264_ = lean_ctor_get(v_ring_1259_, 2);
lean_inc_n(v_u_1264_, 2);
v_semiringInst_1265_ = lean_ctor_get(v_ring_1259_, 4);
lean_inc_ref(v_semiringInst_1265_);
lean_dec_ref(v_ring_1259_);
v___x_1266_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1268_, 0, v_u_1264_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
lean_inc_ref(v___x_1268_);
v___x_1269_ = l_Lean_mkConst(v___x_1266_, v___x_1268_);
v___x_1270_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_1271_ = l_Lean_mkConst(v___x_1270_, v___x_1268_);
v___x_1272_ = l_Lean_mkAppB(v___x_1271_, v_type_1263_, v_semiringInst_1265_);
v_expectedInst_1273_ = l_Lean_mkAppB(v___x_1269_, v_type_1263_, v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_1275_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_1276_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1253_, v_inst_1254_, v_inst_1255_, v_inst_1256_, v_type_1263_, v_u_1264_, v___x_1274_, v___x_1275_, v_expectedInst_1273_);
v___x_1277_ = lean_apply_4(v_toBind_1257_, lean_box(0), lean_box(0), v___x_1276_, v___f_1258_);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_){
_start:
{
lean_object* v_toApplicative_1283_; lean_object* v_toBind_1284_; lean_object* v_getRing_1285_; lean_object* v_modifyRing_1286_; lean_object* v_toPure_1287_; lean_object* v___f_1288_; lean_object* v___f_1289_; lean_object* v___x_1290_; 
v_toApplicative_1283_ = lean_ctor_get(v_inst_1280_, 0);
v_toBind_1284_ = lean_ctor_get(v_inst_1280_, 1);
lean_inc_n(v_toBind_1284_, 3);
v_getRing_1285_ = lean_ctor_get(v_inst_1282_, 0);
lean_inc(v_getRing_1285_);
v_modifyRing_1286_ = lean_ctor_get(v_inst_1282_, 1);
lean_inc(v_modifyRing_1286_);
lean_dec_ref(v_inst_1282_);
v_toPure_1287_ = lean_ctor_get(v_toApplicative_1283_, 1);
lean_inc_n(v_toPure_1287_, 2);
v___f_1288_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1288_, 0, v_toPure_1287_);
lean_closure_set(v___f_1288_, 1, v_modifyRing_1286_);
lean_closure_set(v___f_1288_, 2, v_toBind_1284_);
v___f_1289_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1289_, 0, v_toPure_1287_);
lean_closure_set(v___f_1289_, 1, v_inst_1278_);
lean_closure_set(v___f_1289_, 2, v_inst_1279_);
lean_closure_set(v___f_1289_, 3, v_inst_1280_);
lean_closure_set(v___f_1289_, 4, v_inst_1281_);
lean_closure_set(v___f_1289_, 5, v_toBind_1284_);
lean_closure_set(v___f_1289_, 6, v___f_1288_);
v___x_1290_ = lean_apply_4(v_toBind_1284_, lean_box(0), lean_box(0), v_getRing_1285_, v___f_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn(lean_object* v_m_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_1292_, v_inst_1293_, v_inst_1294_, v_inst_1295_, v_inst_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(lean_object* v_subFn_1298_, lean_object* v_s_1299_){
_start:
{
lean_object* v_id_1300_; lean_object* v_type_1301_; lean_object* v_u_1302_; lean_object* v_ringInst_1303_; lean_object* v_semiringInst_1304_; lean_object* v_charInst_x3f_1305_; uint8_t v_symbolicChar_1306_; lean_object* v_addFn_x3f_1307_; lean_object* v_mulFn_x3f_1308_; lean_object* v_negFn_x3f_1309_; lean_object* v_powFn_x3f_1310_; lean_object* v_intCastFn_x3f_1311_; lean_object* v_natCastFn_x3f_1312_; lean_object* v_natSMulFn_x3f_1313_; lean_object* v_intSMulFn_x3f_1314_; lean_object* v_one_x3f_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1323_; 
v_id_1300_ = lean_ctor_get(v_s_1299_, 0);
v_type_1301_ = lean_ctor_get(v_s_1299_, 1);
v_u_1302_ = lean_ctor_get(v_s_1299_, 2);
v_ringInst_1303_ = lean_ctor_get(v_s_1299_, 3);
v_semiringInst_1304_ = lean_ctor_get(v_s_1299_, 4);
v_charInst_x3f_1305_ = lean_ctor_get(v_s_1299_, 5);
v_symbolicChar_1306_ = lean_ctor_get_uint8(v_s_1299_, sizeof(void*)*16);
v_addFn_x3f_1307_ = lean_ctor_get(v_s_1299_, 6);
v_mulFn_x3f_1308_ = lean_ctor_get(v_s_1299_, 7);
v_negFn_x3f_1309_ = lean_ctor_get(v_s_1299_, 9);
v_powFn_x3f_1310_ = lean_ctor_get(v_s_1299_, 10);
v_intCastFn_x3f_1311_ = lean_ctor_get(v_s_1299_, 11);
v_natCastFn_x3f_1312_ = lean_ctor_get(v_s_1299_, 12);
v_natSMulFn_x3f_1313_ = lean_ctor_get(v_s_1299_, 13);
v_intSMulFn_x3f_1314_ = lean_ctor_get(v_s_1299_, 14);
v_one_x3f_1315_ = lean_ctor_get(v_s_1299_, 15);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_s_1299_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v_s_1299_, 8);
lean_dec(v_unused_1324_);
v___x_1317_ = v_s_1299_;
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_one_x3f_1315_);
lean_inc(v_intSMulFn_x3f_1314_);
lean_inc(v_natSMulFn_x3f_1313_);
lean_inc(v_natCastFn_x3f_1312_);
lean_inc(v_intCastFn_x3f_1311_);
lean_inc(v_powFn_x3f_1310_);
lean_inc(v_negFn_x3f_1309_);
lean_inc(v_mulFn_x3f_1308_);
lean_inc(v_addFn_x3f_1307_);
lean_inc(v_charInst_x3f_1305_);
lean_inc(v_semiringInst_1304_);
lean_inc(v_ringInst_1303_);
lean_inc(v_u_1302_);
lean_inc(v_type_1301_);
lean_inc(v_id_1300_);
lean_dec(v_s_1299_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_subFn_1298_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 8, v___x_1319_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_id_1300_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_type_1301_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_u_1302_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_ringInst_1303_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_semiringInst_1304_);
lean_ctor_set(v_reuseFailAlloc_1322_, 5, v_charInst_x3f_1305_);
lean_ctor_set(v_reuseFailAlloc_1322_, 6, v_addFn_x3f_1307_);
lean_ctor_set(v_reuseFailAlloc_1322_, 7, v_mulFn_x3f_1308_);
lean_ctor_set(v_reuseFailAlloc_1322_, 8, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1322_, 9, v_negFn_x3f_1309_);
lean_ctor_set(v_reuseFailAlloc_1322_, 10, v_powFn_x3f_1310_);
lean_ctor_set(v_reuseFailAlloc_1322_, 11, v_intCastFn_x3f_1311_);
lean_ctor_set(v_reuseFailAlloc_1322_, 12, v_natCastFn_x3f_1312_);
lean_ctor_set(v_reuseFailAlloc_1322_, 13, v_natSMulFn_x3f_1313_);
lean_ctor_set(v_reuseFailAlloc_1322_, 14, v_intSMulFn_x3f_1314_);
lean_ctor_set(v_reuseFailAlloc_1322_, 15, v_one_x3f_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*16, v_symbolicChar_1306_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object* v_toPure_1325_, lean_object* v_subFn_1326_, lean_object* v_____r_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_apply_2(v_toPure_1325_, lean_box(0), v_subFn_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object* v_toPure_1329_, lean_object* v_modifyRing_1330_, lean_object* v_toBind_1331_, lean_object* v_subFn_1332_){
_start:
{
lean_object* v___f_1333_; lean_object* v___f_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_inc_ref(v_subFn_1332_);
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1333_, 0, v_subFn_1332_);
v___f_1334_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1334_, 0, v_toPure_1329_);
lean_closure_set(v___f_1334_, 1, v_subFn_1332_);
v___x_1335_ = lean_apply_1(v_modifyRing_1330_, v___f_1333_);
v___x_1336_ = lean_apply_4(v_toBind_1331_, lean_box(0), lean_box(0), v___x_1335_, v___f_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object* v_toPure_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_toBind_1358_, lean_object* v___f_1359_, lean_object* v_ring_1360_){
_start:
{
lean_object* v_subFn_x3f_1361_; 
v_subFn_x3f_1361_ = lean_ctor_get(v_ring_1360_, 8);
if (lean_obj_tag(v_subFn_x3f_1361_) == 1)
{
lean_object* v_val_1362_; lean_object* v___x_1363_; 
lean_inc_ref(v_subFn_x3f_1361_);
lean_dec_ref(v_ring_1360_);
lean_dec(v___f_1359_);
lean_dec(v_toBind_1358_);
lean_dec_ref(v_inst_1357_);
lean_dec_ref(v_inst_1356_);
lean_dec_ref(v_inst_1355_);
lean_dec(v_inst_1354_);
v_val_1362_ = lean_ctor_get(v_subFn_x3f_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v_subFn_x3f_1361_, 1);
v___x_1363_ = lean_apply_2(v_toPure_1353_, lean_box(0), v_val_1362_);
return v___x_1363_;
}
else
{
lean_object* v_type_1364_; lean_object* v_u_1365_; lean_object* v_ringInst_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_expectedInst_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec(v_toPure_1353_);
v_type_1364_ = lean_ctor_get(v_ring_1360_, 1);
lean_inc_ref_n(v_type_1364_, 3);
v_u_1365_ = lean_ctor_get(v_ring_1360_, 2);
lean_inc_n(v_u_1365_, 2);
v_ringInst_1366_ = lean_ctor_get(v_ring_1360_, 3);
lean_inc_ref(v_ringInst_1366_);
lean_dec_ref(v_ring_1360_);
v___x_1367_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1));
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_u_1365_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
lean_inc_ref(v___x_1369_);
v___x_1370_ = l_Lean_mkConst(v___x_1367_, v___x_1369_);
v___x_1371_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__3));
v___x_1372_ = l_Lean_mkConst(v___x_1371_, v___x_1369_);
v___x_1373_ = l_Lean_mkAppB(v___x_1372_, v_type_1364_, v_ringInst_1366_);
v_expectedInst_1374_ = l_Lean_mkAppB(v___x_1370_, v_type_1364_, v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__5));
v___x_1376_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__7));
v___x_1377_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1354_, v_inst_1355_, v_inst_1356_, v_inst_1357_, v_type_1364_, v_u_1365_, v___x_1375_, v___x_1376_, v_expectedInst_1374_);
v___x_1378_ = lean_apply_4(v_toBind_1358_, lean_box(0), lean_box(0), v___x_1377_, v___f_1359_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_inst_1383_){
_start:
{
lean_object* v_toApplicative_1384_; lean_object* v_toBind_1385_; lean_object* v_getRing_1386_; lean_object* v_modifyRing_1387_; lean_object* v_toPure_1388_; lean_object* v___f_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; 
v_toApplicative_1384_ = lean_ctor_get(v_inst_1381_, 0);
v_toBind_1385_ = lean_ctor_get(v_inst_1381_, 1);
lean_inc_n(v_toBind_1385_, 3);
v_getRing_1386_ = lean_ctor_get(v_inst_1383_, 0);
lean_inc(v_getRing_1386_);
v_modifyRing_1387_ = lean_ctor_get(v_inst_1383_, 1);
lean_inc(v_modifyRing_1387_);
lean_dec_ref(v_inst_1383_);
v_toPure_1388_ = lean_ctor_get(v_toApplicative_1384_, 1);
lean_inc_n(v_toPure_1388_, 2);
v___f_1389_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1389_, 0, v_toPure_1388_);
lean_closure_set(v___f_1389_, 1, v_modifyRing_1387_);
lean_closure_set(v___f_1389_, 2, v_toBind_1385_);
v___f_1390_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1390_, 0, v_toPure_1388_);
lean_closure_set(v___f_1390_, 1, v_inst_1379_);
lean_closure_set(v___f_1390_, 2, v_inst_1380_);
lean_closure_set(v___f_1390_, 3, v_inst_1381_);
lean_closure_set(v___f_1390_, 4, v_inst_1382_);
lean_closure_set(v___f_1390_, 5, v_toBind_1385_);
lean_closure_set(v___f_1390_, 6, v___f_1389_);
v___x_1391_ = lean_apply_4(v_toBind_1385_, lean_box(0), lean_box(0), v_getRing_1386_, v___f_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object* v_m_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_inst_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_1393_, v_inst_1394_, v_inst_1395_, v_inst_1396_, v_inst_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object* v_negFn_1399_, lean_object* v_s_1400_){
_start:
{
lean_object* v_id_1401_; lean_object* v_type_1402_; lean_object* v_u_1403_; lean_object* v_ringInst_1404_; lean_object* v_semiringInst_1405_; lean_object* v_charInst_x3f_1406_; uint8_t v_symbolicChar_1407_; lean_object* v_addFn_x3f_1408_; lean_object* v_mulFn_x3f_1409_; lean_object* v_subFn_x3f_1410_; lean_object* v_powFn_x3f_1411_; lean_object* v_intCastFn_x3f_1412_; lean_object* v_natCastFn_x3f_1413_; lean_object* v_natSMulFn_x3f_1414_; lean_object* v_intSMulFn_x3f_1415_; lean_object* v_one_x3f_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_id_1401_ = lean_ctor_get(v_s_1400_, 0);
v_type_1402_ = lean_ctor_get(v_s_1400_, 1);
v_u_1403_ = lean_ctor_get(v_s_1400_, 2);
v_ringInst_1404_ = lean_ctor_get(v_s_1400_, 3);
v_semiringInst_1405_ = lean_ctor_get(v_s_1400_, 4);
v_charInst_x3f_1406_ = lean_ctor_get(v_s_1400_, 5);
v_symbolicChar_1407_ = lean_ctor_get_uint8(v_s_1400_, sizeof(void*)*16);
v_addFn_x3f_1408_ = lean_ctor_get(v_s_1400_, 6);
v_mulFn_x3f_1409_ = lean_ctor_get(v_s_1400_, 7);
v_subFn_x3f_1410_ = lean_ctor_get(v_s_1400_, 8);
v_powFn_x3f_1411_ = lean_ctor_get(v_s_1400_, 10);
v_intCastFn_x3f_1412_ = lean_ctor_get(v_s_1400_, 11);
v_natCastFn_x3f_1413_ = lean_ctor_get(v_s_1400_, 12);
v_natSMulFn_x3f_1414_ = lean_ctor_get(v_s_1400_, 13);
v_intSMulFn_x3f_1415_ = lean_ctor_get(v_s_1400_, 14);
v_one_x3f_1416_ = lean_ctor_get(v_s_1400_, 15);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_s_1400_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v_s_1400_, 9);
lean_dec(v_unused_1425_);
v___x_1418_ = v_s_1400_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_one_x3f_1416_);
lean_inc(v_intSMulFn_x3f_1415_);
lean_inc(v_natSMulFn_x3f_1414_);
lean_inc(v_natCastFn_x3f_1413_);
lean_inc(v_intCastFn_x3f_1412_);
lean_inc(v_powFn_x3f_1411_);
lean_inc(v_subFn_x3f_1410_);
lean_inc(v_mulFn_x3f_1409_);
lean_inc(v_addFn_x3f_1408_);
lean_inc(v_charInst_x3f_1406_);
lean_inc(v_semiringInst_1405_);
lean_inc(v_ringInst_1404_);
lean_inc(v_u_1403_);
lean_inc(v_type_1402_);
lean_inc(v_id_1401_);
lean_dec(v_s_1400_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_negFn_1399_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 9, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_id_1401_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_type_1402_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_u_1403_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_ringInst_1404_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_semiringInst_1405_);
lean_ctor_set(v_reuseFailAlloc_1423_, 5, v_charInst_x3f_1406_);
lean_ctor_set(v_reuseFailAlloc_1423_, 6, v_addFn_x3f_1408_);
lean_ctor_set(v_reuseFailAlloc_1423_, 7, v_mulFn_x3f_1409_);
lean_ctor_set(v_reuseFailAlloc_1423_, 8, v_subFn_x3f_1410_);
lean_ctor_set(v_reuseFailAlloc_1423_, 9, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1423_, 10, v_powFn_x3f_1411_);
lean_ctor_set(v_reuseFailAlloc_1423_, 11, v_intCastFn_x3f_1412_);
lean_ctor_set(v_reuseFailAlloc_1423_, 12, v_natCastFn_x3f_1413_);
lean_ctor_set(v_reuseFailAlloc_1423_, 13, v_natSMulFn_x3f_1414_);
lean_ctor_set(v_reuseFailAlloc_1423_, 14, v_intSMulFn_x3f_1415_);
lean_ctor_set(v_reuseFailAlloc_1423_, 15, v_one_x3f_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*16, v_symbolicChar_1407_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object* v_toPure_1426_, lean_object* v_negFn_1427_, lean_object* v_____r_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_apply_2(v_toPure_1426_, lean_box(0), v_negFn_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object* v_toPure_1430_, lean_object* v_modifyRing_1431_, lean_object* v_toBind_1432_, lean_object* v_negFn_1433_){
_start:
{
lean_object* v___f_1434_; lean_object* v___f_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_inc_ref(v_negFn_1433_);
v___f_1434_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1434_, 0, v_negFn_1433_);
v___f_1435_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1435_, 0, v_toPure_1430_);
lean_closure_set(v___f_1435_, 1, v_negFn_1433_);
v___x_1436_ = lean_apply_1(v_modifyRing_1431_, v___f_1434_);
v___x_1437_ = lean_apply_4(v_toBind_1432_, lean_box(0), lean_box(0), v___x_1436_, v___f_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object* v_toPure_1451_, lean_object* v_inst_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_toBind_1456_, lean_object* v___f_1457_, lean_object* v_ring_1458_){
_start:
{
lean_object* v_negFn_x3f_1459_; 
v_negFn_x3f_1459_ = lean_ctor_get(v_ring_1458_, 9);
if (lean_obj_tag(v_negFn_x3f_1459_) == 1)
{
lean_object* v_val_1460_; lean_object* v___x_1461_; 
lean_inc_ref(v_negFn_x3f_1459_);
lean_dec_ref(v_ring_1458_);
lean_dec(v___f_1457_);
lean_dec(v_toBind_1456_);
lean_dec_ref(v_inst_1455_);
lean_dec_ref(v_inst_1454_);
lean_dec_ref(v_inst_1453_);
lean_dec(v_inst_1452_);
v_val_1460_ = lean_ctor_get(v_negFn_x3f_1459_, 0);
lean_inc(v_val_1460_);
lean_dec_ref_known(v_negFn_x3f_1459_, 1);
v___x_1461_ = lean_apply_2(v_toPure_1451_, lean_box(0), v_val_1460_);
return v___x_1461_;
}
else
{
lean_object* v_type_1462_; lean_object* v_u_1463_; lean_object* v_ringInst_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v_expectedInst_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_toPure_1451_);
v_type_1462_ = lean_ctor_get(v_ring_1458_, 1);
lean_inc_ref_n(v_type_1462_, 2);
v_u_1463_ = lean_ctor_get(v_ring_1458_, 2);
lean_inc_n(v_u_1463_, 2);
v_ringInst_1464_ = lean_ctor_get(v_ring_1458_, 3);
lean_inc_ref(v_ringInst_1464_);
lean_dec_ref(v_ring_1458_);
v___x_1465_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1));
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_u_1463_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = l_Lean_mkConst(v___x_1465_, v___x_1467_);
v_expectedInst_1469_ = l_Lean_mkAppB(v___x_1468_, v_type_1462_, v_ringInst_1464_);
v___x_1470_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3));
v___x_1471_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5));
v___x_1472_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1452_, v_inst_1453_, v_inst_1454_, v_inst_1455_, v_type_1462_, v_u_1463_, v___x_1470_, v___x_1471_, v_expectedInst_1469_);
v___x_1473_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1472_, v___f_1457_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object* v_inst_1474_, lean_object* v_inst_1475_, lean_object* v_inst_1476_, lean_object* v_inst_1477_, lean_object* v_inst_1478_){
_start:
{
lean_object* v_toApplicative_1479_; lean_object* v_toBind_1480_; lean_object* v_getRing_1481_; lean_object* v_modifyRing_1482_; lean_object* v_toPure_1483_; lean_object* v___f_1484_; lean_object* v___f_1485_; lean_object* v___x_1486_; 
v_toApplicative_1479_ = lean_ctor_get(v_inst_1476_, 0);
v_toBind_1480_ = lean_ctor_get(v_inst_1476_, 1);
lean_inc_n(v_toBind_1480_, 3);
v_getRing_1481_ = lean_ctor_get(v_inst_1478_, 0);
lean_inc(v_getRing_1481_);
v_modifyRing_1482_ = lean_ctor_get(v_inst_1478_, 1);
lean_inc(v_modifyRing_1482_);
lean_dec_ref(v_inst_1478_);
v_toPure_1483_ = lean_ctor_get(v_toApplicative_1479_, 1);
lean_inc_n(v_toPure_1483_, 2);
v___f_1484_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1484_, 0, v_toPure_1483_);
lean_closure_set(v___f_1484_, 1, v_modifyRing_1482_);
lean_closure_set(v___f_1484_, 2, v_toBind_1480_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1485_, 0, v_toPure_1483_);
lean_closure_set(v___f_1485_, 1, v_inst_1474_);
lean_closure_set(v___f_1485_, 2, v_inst_1475_);
lean_closure_set(v___f_1485_, 3, v_inst_1476_);
lean_closure_set(v___f_1485_, 4, v_inst_1477_);
lean_closure_set(v___f_1485_, 5, v_toBind_1480_);
lean_closure_set(v___f_1485_, 6, v___f_1484_);
v___x_1486_ = lean_apply_4(v_toBind_1480_, lean_box(0), lean_box(0), v_getRing_1481_, v___f_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object* v_m_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_1488_, v_inst_1489_, v_inst_1490_, v_inst_1491_, v_inst_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object* v_powFn_1494_, lean_object* v_s_1495_){
_start:
{
lean_object* v_id_1496_; lean_object* v_type_1497_; lean_object* v_u_1498_; lean_object* v_ringInst_1499_; lean_object* v_semiringInst_1500_; lean_object* v_charInst_x3f_1501_; uint8_t v_symbolicChar_1502_; lean_object* v_addFn_x3f_1503_; lean_object* v_mulFn_x3f_1504_; lean_object* v_subFn_x3f_1505_; lean_object* v_negFn_x3f_1506_; lean_object* v_intCastFn_x3f_1507_; lean_object* v_natCastFn_x3f_1508_; lean_object* v_natSMulFn_x3f_1509_; lean_object* v_intSMulFn_x3f_1510_; lean_object* v_one_x3f_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1519_; 
v_id_1496_ = lean_ctor_get(v_s_1495_, 0);
v_type_1497_ = lean_ctor_get(v_s_1495_, 1);
v_u_1498_ = lean_ctor_get(v_s_1495_, 2);
v_ringInst_1499_ = lean_ctor_get(v_s_1495_, 3);
v_semiringInst_1500_ = lean_ctor_get(v_s_1495_, 4);
v_charInst_x3f_1501_ = lean_ctor_get(v_s_1495_, 5);
v_symbolicChar_1502_ = lean_ctor_get_uint8(v_s_1495_, sizeof(void*)*16);
v_addFn_x3f_1503_ = lean_ctor_get(v_s_1495_, 6);
v_mulFn_x3f_1504_ = lean_ctor_get(v_s_1495_, 7);
v_subFn_x3f_1505_ = lean_ctor_get(v_s_1495_, 8);
v_negFn_x3f_1506_ = lean_ctor_get(v_s_1495_, 9);
v_intCastFn_x3f_1507_ = lean_ctor_get(v_s_1495_, 11);
v_natCastFn_x3f_1508_ = lean_ctor_get(v_s_1495_, 12);
v_natSMulFn_x3f_1509_ = lean_ctor_get(v_s_1495_, 13);
v_intSMulFn_x3f_1510_ = lean_ctor_get(v_s_1495_, 14);
v_one_x3f_1511_ = lean_ctor_get(v_s_1495_, 15);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_s_1495_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_s_1495_, 10);
lean_dec(v_unused_1520_);
v___x_1513_ = v_s_1495_;
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_one_x3f_1511_);
lean_inc(v_intSMulFn_x3f_1510_);
lean_inc(v_natSMulFn_x3f_1509_);
lean_inc(v_natCastFn_x3f_1508_);
lean_inc(v_intCastFn_x3f_1507_);
lean_inc(v_negFn_x3f_1506_);
lean_inc(v_subFn_x3f_1505_);
lean_inc(v_mulFn_x3f_1504_);
lean_inc(v_addFn_x3f_1503_);
lean_inc(v_charInst_x3f_1501_);
lean_inc(v_semiringInst_1500_);
lean_inc(v_ringInst_1499_);
lean_inc(v_u_1498_);
lean_inc(v_type_1497_);
lean_inc(v_id_1496_);
lean_dec(v_s_1495_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1515_, 0, v_powFn_1494_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 10, v___x_1515_);
v___x_1517_ = v___x_1513_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_id_1496_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_type_1497_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_u_1498_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_ringInst_1499_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_semiringInst_1500_);
lean_ctor_set(v_reuseFailAlloc_1518_, 5, v_charInst_x3f_1501_);
lean_ctor_set(v_reuseFailAlloc_1518_, 6, v_addFn_x3f_1503_);
lean_ctor_set(v_reuseFailAlloc_1518_, 7, v_mulFn_x3f_1504_);
lean_ctor_set(v_reuseFailAlloc_1518_, 8, v_subFn_x3f_1505_);
lean_ctor_set(v_reuseFailAlloc_1518_, 9, v_negFn_x3f_1506_);
lean_ctor_set(v_reuseFailAlloc_1518_, 10, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1518_, 11, v_intCastFn_x3f_1507_);
lean_ctor_set(v_reuseFailAlloc_1518_, 12, v_natCastFn_x3f_1508_);
lean_ctor_set(v_reuseFailAlloc_1518_, 13, v_natSMulFn_x3f_1509_);
lean_ctor_set(v_reuseFailAlloc_1518_, 14, v_intSMulFn_x3f_1510_);
lean_ctor_set(v_reuseFailAlloc_1518_, 15, v_one_x3f_1511_);
lean_ctor_set_uint8(v_reuseFailAlloc_1518_, sizeof(void*)*16, v_symbolicChar_1502_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object* v_toPure_1521_, lean_object* v_powFn_1522_, lean_object* v_____r_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_apply_2(v_toPure_1521_, lean_box(0), v_powFn_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object* v_toPure_1525_, lean_object* v_modifyRing_1526_, lean_object* v_toBind_1527_, lean_object* v_powFn_1528_){
_start:
{
lean_object* v___f_1529_; lean_object* v___f_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_inc_ref(v_powFn_1528_);
v___f_1529_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1529_, 0, v_powFn_1528_);
v___f_1530_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1530_, 0, v_toPure_1525_);
lean_closure_set(v___f_1530_, 1, v_powFn_1528_);
v___x_1531_ = lean_apply_1(v_modifyRing_1526_, v___f_1529_);
v___x_1532_ = lean_apply_4(v_toBind_1527_, lean_box(0), lean_box(0), v___x_1531_, v___f_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object* v_toPure_1533_, lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_toBind_1538_, lean_object* v___f_1539_, lean_object* v_ring_1540_){
_start:
{
lean_object* v_powFn_x3f_1541_; 
v_powFn_x3f_1541_ = lean_ctor_get(v_ring_1540_, 10);
if (lean_obj_tag(v_powFn_x3f_1541_) == 1)
{
lean_object* v_val_1542_; lean_object* v___x_1543_; 
lean_inc_ref(v_powFn_x3f_1541_);
lean_dec_ref(v_ring_1540_);
lean_dec(v___f_1539_);
lean_dec(v_toBind_1538_);
lean_dec_ref(v_inst_1537_);
lean_dec_ref(v_inst_1536_);
lean_dec_ref(v_inst_1535_);
lean_dec(v_inst_1534_);
v_val_1542_ = lean_ctor_get(v_powFn_x3f_1541_, 0);
lean_inc(v_val_1542_);
lean_dec_ref_known(v_powFn_x3f_1541_, 1);
v___x_1543_ = lean_apply_2(v_toPure_1533_, lean_box(0), v_val_1542_);
return v___x_1543_;
}
else
{
lean_object* v_type_1544_; lean_object* v_u_1545_; lean_object* v_semiringInst_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec(v_toPure_1533_);
v_type_1544_ = lean_ctor_get(v_ring_1540_, 1);
lean_inc_ref(v_type_1544_);
v_u_1545_ = lean_ctor_get(v_ring_1540_, 2);
lean_inc(v_u_1545_);
v_semiringInst_1546_ = lean_ctor_get(v_ring_1540_, 4);
lean_inc_ref(v_semiringInst_1546_);
lean_dec_ref(v_ring_1540_);
v___x_1547_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1534_, v_inst_1535_, v_inst_1536_, v_inst_1537_, v_u_1545_, v_type_1544_, v_semiringInst_1546_);
v___x_1548_ = lean_apply_4(v_toBind_1538_, lean_box(0), lean_box(0), v___x_1547_, v___f_1539_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object* v_inst_1549_, lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_){
_start:
{
lean_object* v_toApplicative_1554_; lean_object* v_toBind_1555_; lean_object* v_getRing_1556_; lean_object* v_modifyRing_1557_; lean_object* v_toPure_1558_; lean_object* v___f_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; 
v_toApplicative_1554_ = lean_ctor_get(v_inst_1551_, 0);
v_toBind_1555_ = lean_ctor_get(v_inst_1551_, 1);
lean_inc_n(v_toBind_1555_, 3);
v_getRing_1556_ = lean_ctor_get(v_inst_1553_, 0);
lean_inc(v_getRing_1556_);
v_modifyRing_1557_ = lean_ctor_get(v_inst_1553_, 1);
lean_inc(v_modifyRing_1557_);
lean_dec_ref(v_inst_1553_);
v_toPure_1558_ = lean_ctor_get(v_toApplicative_1554_, 1);
lean_inc_n(v_toPure_1558_, 2);
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1559_, 0, v_toPure_1558_);
lean_closure_set(v___f_1559_, 1, v_modifyRing_1557_);
lean_closure_set(v___f_1559_, 2, v_toBind_1555_);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1560_, 0, v_toPure_1558_);
lean_closure_set(v___f_1560_, 1, v_inst_1549_);
lean_closure_set(v___f_1560_, 2, v_inst_1550_);
lean_closure_set(v___f_1560_, 3, v_inst_1551_);
lean_closure_set(v___f_1560_, 4, v_inst_1552_);
lean_closure_set(v___f_1560_, 5, v_toBind_1555_);
lean_closure_set(v___f_1560_, 6, v___f_1559_);
v___x_1561_ = lean_apply_4(v_toBind_1555_, lean_box(0), lean_box(0), v_getRing_1556_, v___f_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object* v_m_1562_, lean_object* v_inst_1563_, lean_object* v_inst_1564_, lean_object* v_inst_1565_, lean_object* v_inst_1566_, lean_object* v_inst_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_1563_, v_inst_1564_, v_inst_1565_, v_inst_1566_, v_inst_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_1569_, lean_object* v_s_1570_){
_start:
{
lean_object* v_id_1571_; lean_object* v_type_1572_; lean_object* v_u_1573_; lean_object* v_ringInst_1574_; lean_object* v_semiringInst_1575_; lean_object* v_charInst_x3f_1576_; uint8_t v_symbolicChar_1577_; lean_object* v_addFn_x3f_1578_; lean_object* v_mulFn_x3f_1579_; lean_object* v_subFn_x3f_1580_; lean_object* v_negFn_x3f_1581_; lean_object* v_powFn_x3f_1582_; lean_object* v_natCastFn_x3f_1583_; lean_object* v_natSMulFn_x3f_1584_; lean_object* v_intSMulFn_x3f_1585_; lean_object* v_one_x3f_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1594_; 
v_id_1571_ = lean_ctor_get(v_s_1570_, 0);
v_type_1572_ = lean_ctor_get(v_s_1570_, 1);
v_u_1573_ = lean_ctor_get(v_s_1570_, 2);
v_ringInst_1574_ = lean_ctor_get(v_s_1570_, 3);
v_semiringInst_1575_ = lean_ctor_get(v_s_1570_, 4);
v_charInst_x3f_1576_ = lean_ctor_get(v_s_1570_, 5);
v_symbolicChar_1577_ = lean_ctor_get_uint8(v_s_1570_, sizeof(void*)*16);
v_addFn_x3f_1578_ = lean_ctor_get(v_s_1570_, 6);
v_mulFn_x3f_1579_ = lean_ctor_get(v_s_1570_, 7);
v_subFn_x3f_1580_ = lean_ctor_get(v_s_1570_, 8);
v_negFn_x3f_1581_ = lean_ctor_get(v_s_1570_, 9);
v_powFn_x3f_1582_ = lean_ctor_get(v_s_1570_, 10);
v_natCastFn_x3f_1583_ = lean_ctor_get(v_s_1570_, 12);
v_natSMulFn_x3f_1584_ = lean_ctor_get(v_s_1570_, 13);
v_intSMulFn_x3f_1585_ = lean_ctor_get(v_s_1570_, 14);
v_one_x3f_1586_ = lean_ctor_get(v_s_1570_, 15);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_s_1570_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v_s_1570_, 11);
lean_dec(v_unused_1595_);
v___x_1588_ = v_s_1570_;
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_one_x3f_1586_);
lean_inc(v_intSMulFn_x3f_1585_);
lean_inc(v_natSMulFn_x3f_1584_);
lean_inc(v_natCastFn_x3f_1583_);
lean_inc(v_powFn_x3f_1582_);
lean_inc(v_negFn_x3f_1581_);
lean_inc(v_subFn_x3f_1580_);
lean_inc(v_mulFn_x3f_1579_);
lean_inc(v_addFn_x3f_1578_);
lean_inc(v_charInst_x3f_1576_);
lean_inc(v_semiringInst_1575_);
lean_inc(v_ringInst_1574_);
lean_inc(v_u_1573_);
lean_inc(v_type_1572_);
lean_inc(v_id_1571_);
lean_dec(v_s_1570_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v_intCastFn_1569_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 11, v___x_1590_);
v___x_1592_ = v___x_1588_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_id_1571_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_type_1572_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_u_1573_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_ringInst_1574_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_semiringInst_1575_);
lean_ctor_set(v_reuseFailAlloc_1593_, 5, v_charInst_x3f_1576_);
lean_ctor_set(v_reuseFailAlloc_1593_, 6, v_addFn_x3f_1578_);
lean_ctor_set(v_reuseFailAlloc_1593_, 7, v_mulFn_x3f_1579_);
lean_ctor_set(v_reuseFailAlloc_1593_, 8, v_subFn_x3f_1580_);
lean_ctor_set(v_reuseFailAlloc_1593_, 9, v_negFn_x3f_1581_);
lean_ctor_set(v_reuseFailAlloc_1593_, 10, v_powFn_x3f_1582_);
lean_ctor_set(v_reuseFailAlloc_1593_, 11, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1593_, 12, v_natCastFn_x3f_1583_);
lean_ctor_set(v_reuseFailAlloc_1593_, 13, v_natSMulFn_x3f_1584_);
lean_ctor_set(v_reuseFailAlloc_1593_, 14, v_intSMulFn_x3f_1585_);
lean_ctor_set(v_reuseFailAlloc_1593_, 15, v_one_x3f_1586_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*16, v_symbolicChar_1577_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object* v_toPure_1596_, lean_object* v_intCastFn_1597_, lean_object* v_____r_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_apply_2(v_toPure_1596_, lean_box(0), v_intCastFn_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object* v_toPure_1600_, lean_object* v_modifyRing_1601_, lean_object* v_toBind_1602_, lean_object* v_intCastFn_1603_){
_start:
{
lean_object* v___f_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_inc_ref(v_intCastFn_1603_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1604_, 0, v_intCastFn_1603_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1605_, 0, v_toPure_1600_);
lean_closure_set(v___f_1605_, 1, v_intCastFn_1603_);
v___x_1606_ = lean_apply_1(v_modifyRing_1601_, v___f_1604_);
v___x_1607_ = lean_apply_4(v_toBind_1602_, lean_box(0), lean_box(0), v___x_1606_, v___f_1605_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v_type_1611_, lean_object* v_canonExpr_1612_, lean_object* v_toBind_1613_, lean_object* v___f_1614_, lean_object* v_inst_1615_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1616_ = l_Lean_Name_mkStr2(v___x_1608_, v___x_1609_);
v___x_1617_ = l_Lean_mkConst(v___x_1616_, v___x_1610_);
v___x_1618_ = l_Lean_mkAppB(v___x_1617_, v_type_1611_, v_inst_1615_);
v___x_1619_ = lean_apply_1(v_canonExpr_1612_, v___x_1618_);
v___x_1620_ = lean_apply_4(v_toBind_1613_, lean_box(0), lean_box(0), v___x_1619_, v___f_1614_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object* v_toPure_1626_, lean_object* v_inst_x27_1627_, lean_object* v_toBind_1628_, lean_object* v___f_1629_, lean_object* v___f_1630_, lean_object* v_inst_1631_, lean_object* v_____do__lift_1632_){
_start:
{
if (lean_obj_tag(v_____do__lift_1632_) == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec(v_inst_1631_);
lean_dec(v___f_1630_);
v___x_1633_ = lean_apply_2(v_toPure_1626_, lean_box(0), v_inst_x27_1627_);
v___x_1634_ = lean_apply_4(v_toBind_1628_, lean_box(0), lean_box(0), v___x_1633_, v___f_1629_);
return v___x_1634_;
}
else
{
lean_object* v_val_1635_; lean_object* v___f_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec(v___f_1629_);
v_val_1635_ = lean_ctor_get(v_____do__lift_1632_, 0);
lean_inc_n(v_val_1635_, 2);
lean_dec_ref_known(v_____do__lift_1632_, 1);
lean_inc(v_toBind_1628_);
v___f_1636_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1636_, 0, v_toPure_1626_);
lean_closure_set(v___f_1636_, 1, v_val_1635_);
lean_closure_set(v___f_1636_, 2, v_toBind_1628_);
lean_closure_set(v___f_1636_, 3, v___f_1630_);
v___x_1637_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2));
v___x_1638_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_1638_, 0, v___x_1637_);
lean_closure_set(v___x_1638_, 1, v_val_1635_);
lean_closure_set(v___x_1638_, 2, v_inst_x27_1627_);
v___x_1639_ = lean_apply_2(v_inst_1631_, lean_box(0), v___x_1638_);
v___x_1640_ = lean_apply_4(v_toBind_1628_, lean_box(0), lean_box(0), v___x_1639_, v___f_1636_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object* v_toPure_1650_, lean_object* v_inst_1651_, lean_object* v_toBind_1652_, lean_object* v___f_1653_, lean_object* v_inst_1654_, lean_object* v_ring_1655_){
_start:
{
lean_object* v_intCastFn_x3f_1656_; 
v_intCastFn_x3f_1656_ = lean_ctor_get(v_ring_1655_, 11);
if (lean_obj_tag(v_intCastFn_x3f_1656_) == 1)
{
lean_object* v_val_1657_; lean_object* v___x_1658_; 
lean_inc_ref(v_intCastFn_x3f_1656_);
lean_dec_ref(v_ring_1655_);
lean_dec(v_inst_1654_);
lean_dec(v___f_1653_);
lean_dec(v_toBind_1652_);
lean_dec_ref(v_inst_1651_);
v_val_1657_ = lean_ctor_get(v_intCastFn_x3f_1656_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v_intCastFn_x3f_1656_, 1);
v___x_1658_ = lean_apply_2(v_toPure_1650_, lean_box(0), v_val_1657_);
return v___x_1658_;
}
else
{
lean_object* v_type_1659_; lean_object* v_u_1660_; lean_object* v_ringInst_1661_; lean_object* v_canonExpr_1662_; lean_object* v_synthInstance_x3f_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1684_; 
v_type_1659_ = lean_ctor_get(v_ring_1655_, 1);
lean_inc_ref(v_type_1659_);
v_u_1660_ = lean_ctor_get(v_ring_1655_, 2);
lean_inc(v_u_1660_);
v_ringInst_1661_ = lean_ctor_get(v_ring_1655_, 3);
lean_inc_ref(v_ringInst_1661_);
lean_dec_ref(v_ring_1655_);
v_canonExpr_1662_ = lean_ctor_get(v_inst_1651_, 0);
v_synthInstance_x3f_1663_ = lean_ctor_get(v_inst_1651_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_inst_1651_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1665_ = v_inst_1651_;
v_isShared_1666_ = v_isSharedCheck_1684_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_synthInstance_x3f_1663_);
lean_inc(v_canonExpr_1662_);
lean_dec(v_inst_1651_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1684_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1667_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0));
v___x_1668_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1));
v___x_1669_ = lean_box(0);
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 1);
lean_ctor_set(v___x_1665_, 1, v___x_1669_);
lean_ctor_set(v___x_1665_, 0, v_u_1660_);
v___x_1671_ = v___x_1665_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_u_1660_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; lean_object* v_inst_x27_1673_; lean_object* v___x_1674_; lean_object* v___f_1675_; lean_object* v___f_1676_; lean_object* v___f_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_instType_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_inc_ref_n(v___x_1671_, 2);
v___x_1672_ = l_Lean_mkConst(v___x_1668_, v___x_1671_);
lean_inc_ref_n(v_type_1659_, 2);
v_inst_x27_1673_ = l_Lean_mkAppB(v___x_1672_, v_type_1659_, v_ringInst_1661_);
v___x_1674_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_1652_, 2);
v___f_1675_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1675_, 0, v___x_1674_);
lean_closure_set(v___f_1675_, 1, v___x_1667_);
lean_closure_set(v___f_1675_, 2, v___x_1671_);
lean_closure_set(v___f_1675_, 3, v_type_1659_);
lean_closure_set(v___f_1675_, 4, v_canonExpr_1662_);
lean_closure_set(v___f_1675_, 5, v_toBind_1652_);
lean_closure_set(v___f_1675_, 6, v___f_1653_);
v___f_1676_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1676_, 0, v___f_1675_);
lean_inc_ref(v___f_1676_);
v___f_1677_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_1677_, 0, v_toPure_1650_);
lean_closure_set(v___f_1677_, 1, v_inst_x27_1673_);
lean_closure_set(v___f_1677_, 2, v_toBind_1652_);
lean_closure_set(v___f_1677_, 3, v___f_1676_);
lean_closure_set(v___f_1677_, 4, v___f_1676_);
lean_closure_set(v___f_1677_, 5, v_inst_1654_);
v___x_1678_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3));
v___x_1679_ = l_Lean_mkConst(v___x_1678_, v___x_1671_);
v_instType_1680_ = l_Lean_Expr_app___override(v___x_1679_, v_type_1659_);
v___x_1681_ = lean_apply_1(v_synthInstance_x3f_1663_, v_instType_1680_);
v___x_1682_ = lean_apply_4(v_toBind_1652_, lean_box(0), lean_box(0), v___x_1681_, v___f_1677_);
return v___x_1682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_inst_1688_){
_start:
{
lean_object* v_toApplicative_1689_; lean_object* v_toBind_1690_; lean_object* v_getRing_1691_; lean_object* v_modifyRing_1692_; lean_object* v_toPure_1693_; lean_object* v___f_1694_; lean_object* v___f_1695_; lean_object* v___x_1696_; 
v_toApplicative_1689_ = lean_ctor_get(v_inst_1686_, 0);
lean_inc_ref(v_toApplicative_1689_);
v_toBind_1690_ = lean_ctor_get(v_inst_1686_, 1);
lean_inc_n(v_toBind_1690_, 3);
lean_dec_ref(v_inst_1686_);
v_getRing_1691_ = lean_ctor_get(v_inst_1688_, 0);
lean_inc(v_getRing_1691_);
v_modifyRing_1692_ = lean_ctor_get(v_inst_1688_, 1);
lean_inc(v_modifyRing_1692_);
lean_dec_ref(v_inst_1688_);
v_toPure_1693_ = lean_ctor_get(v_toApplicative_1689_, 1);
lean_inc_n(v_toPure_1693_, 2);
lean_dec_ref(v_toApplicative_1689_);
v___f_1694_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1694_, 0, v_toPure_1693_);
lean_closure_set(v___f_1694_, 1, v_modifyRing_1692_);
lean_closure_set(v___f_1694_, 2, v_toBind_1690_);
v___f_1695_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_1695_, 0, v_toPure_1693_);
lean_closure_set(v___f_1695_, 1, v_inst_1687_);
lean_closure_set(v___f_1695_, 2, v_toBind_1690_);
lean_closure_set(v___f_1695_, 3, v___f_1694_);
lean_closure_set(v___f_1695_, 4, v_inst_1685_);
v___x_1696_ = lean_apply_4(v_toBind_1690_, lean_box(0), lean_box(0), v_getRing_1691_, v___f_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object* v_m_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_1698_, v_inst_1699_, v_inst_1700_, v_inst_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_1703_, lean_object* v_s_1704_){
_start:
{
lean_object* v_id_1705_; lean_object* v_type_1706_; lean_object* v_u_1707_; lean_object* v_ringInst_1708_; lean_object* v_semiringInst_1709_; lean_object* v_charInst_x3f_1710_; uint8_t v_symbolicChar_1711_; lean_object* v_addFn_x3f_1712_; lean_object* v_mulFn_x3f_1713_; lean_object* v_subFn_x3f_1714_; lean_object* v_negFn_x3f_1715_; lean_object* v_powFn_x3f_1716_; lean_object* v_intCastFn_x3f_1717_; lean_object* v_natSMulFn_x3f_1718_; lean_object* v_intSMulFn_x3f_1719_; lean_object* v_one_x3f_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1728_; 
v_id_1705_ = lean_ctor_get(v_s_1704_, 0);
v_type_1706_ = lean_ctor_get(v_s_1704_, 1);
v_u_1707_ = lean_ctor_get(v_s_1704_, 2);
v_ringInst_1708_ = lean_ctor_get(v_s_1704_, 3);
v_semiringInst_1709_ = lean_ctor_get(v_s_1704_, 4);
v_charInst_x3f_1710_ = lean_ctor_get(v_s_1704_, 5);
v_symbolicChar_1711_ = lean_ctor_get_uint8(v_s_1704_, sizeof(void*)*16);
v_addFn_x3f_1712_ = lean_ctor_get(v_s_1704_, 6);
v_mulFn_x3f_1713_ = lean_ctor_get(v_s_1704_, 7);
v_subFn_x3f_1714_ = lean_ctor_get(v_s_1704_, 8);
v_negFn_x3f_1715_ = lean_ctor_get(v_s_1704_, 9);
v_powFn_x3f_1716_ = lean_ctor_get(v_s_1704_, 10);
v_intCastFn_x3f_1717_ = lean_ctor_get(v_s_1704_, 11);
v_natSMulFn_x3f_1718_ = lean_ctor_get(v_s_1704_, 13);
v_intSMulFn_x3f_1719_ = lean_ctor_get(v_s_1704_, 14);
v_one_x3f_1720_ = lean_ctor_get(v_s_1704_, 15);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_s_1704_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v_s_1704_, 12);
lean_dec(v_unused_1729_);
v___x_1722_ = v_s_1704_;
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_one_x3f_1720_);
lean_inc(v_intSMulFn_x3f_1719_);
lean_inc(v_natSMulFn_x3f_1718_);
lean_inc(v_intCastFn_x3f_1717_);
lean_inc(v_powFn_x3f_1716_);
lean_inc(v_negFn_x3f_1715_);
lean_inc(v_subFn_x3f_1714_);
lean_inc(v_mulFn_x3f_1713_);
lean_inc(v_addFn_x3f_1712_);
lean_inc(v_charInst_x3f_1710_);
lean_inc(v_semiringInst_1709_);
lean_inc(v_ringInst_1708_);
lean_inc(v_u_1707_);
lean_inc(v_type_1706_);
lean_inc(v_id_1705_);
lean_dec(v_s_1704_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_natCastFn_1703_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 12, v___x_1724_);
v___x_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_id_1705_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_type_1706_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_u_1707_);
lean_ctor_set(v_reuseFailAlloc_1727_, 3, v_ringInst_1708_);
lean_ctor_set(v_reuseFailAlloc_1727_, 4, v_semiringInst_1709_);
lean_ctor_set(v_reuseFailAlloc_1727_, 5, v_charInst_x3f_1710_);
lean_ctor_set(v_reuseFailAlloc_1727_, 6, v_addFn_x3f_1712_);
lean_ctor_set(v_reuseFailAlloc_1727_, 7, v_mulFn_x3f_1713_);
lean_ctor_set(v_reuseFailAlloc_1727_, 8, v_subFn_x3f_1714_);
lean_ctor_set(v_reuseFailAlloc_1727_, 9, v_negFn_x3f_1715_);
lean_ctor_set(v_reuseFailAlloc_1727_, 10, v_powFn_x3f_1716_);
lean_ctor_set(v_reuseFailAlloc_1727_, 11, v_intCastFn_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1727_, 12, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1727_, 13, v_natSMulFn_x3f_1718_);
lean_ctor_set(v_reuseFailAlloc_1727_, 14, v_intSMulFn_x3f_1719_);
lean_ctor_set(v_reuseFailAlloc_1727_, 15, v_one_x3f_1720_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, sizeof(void*)*16, v_symbolicChar_1711_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1730_, lean_object* v_natCastFn_1731_, lean_object* v_____r_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_apply_2(v_toPure_1730_, lean_box(0), v_natCastFn_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1734_, lean_object* v_modifyRing_1735_, lean_object* v_toBind_1736_, lean_object* v_natCastFn_1737_){
_start:
{
lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_inc_ref(v_natCastFn_1737_);
v___f_1738_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1738_, 0, v_natCastFn_1737_);
v___f_1739_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1739_, 0, v_toPure_1734_);
lean_closure_set(v___f_1739_, 1, v_natCastFn_1737_);
v___x_1740_ = lean_apply_1(v_modifyRing_1735_, v___f_1738_);
v___x_1741_ = lean_apply_4(v_toBind_1736_, lean_box(0), lean_box(0), v___x_1740_, v___f_1739_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1742_, lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_toBind_1746_, lean_object* v___f_1747_, lean_object* v_ring_1748_){
_start:
{
lean_object* v_natCastFn_x3f_1749_; 
v_natCastFn_x3f_1749_ = lean_ctor_get(v_ring_1748_, 12);
if (lean_obj_tag(v_natCastFn_x3f_1749_) == 1)
{
lean_object* v_val_1750_; lean_object* v___x_1751_; 
lean_inc_ref(v_natCastFn_x3f_1749_);
lean_dec_ref(v_ring_1748_);
lean_dec(v___f_1747_);
lean_dec(v_toBind_1746_);
lean_dec_ref(v_inst_1745_);
lean_dec_ref(v_inst_1744_);
lean_dec(v_inst_1743_);
v_val_1750_ = lean_ctor_get(v_natCastFn_x3f_1749_, 0);
lean_inc(v_val_1750_);
lean_dec_ref_known(v_natCastFn_x3f_1749_, 1);
v___x_1751_ = lean_apply_2(v_toPure_1742_, lean_box(0), v_val_1750_);
return v___x_1751_;
}
else
{
lean_object* v_type_1752_; lean_object* v_u_1753_; lean_object* v_semiringInst_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_toPure_1742_);
v_type_1752_ = lean_ctor_get(v_ring_1748_, 1);
lean_inc_ref(v_type_1752_);
v_u_1753_ = lean_ctor_get(v_ring_1748_, 2);
lean_inc(v_u_1753_);
v_semiringInst_1754_ = lean_ctor_get(v_ring_1748_, 4);
lean_inc_ref(v_semiringInst_1754_);
lean_dec_ref(v_ring_1748_);
v___x_1755_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1743_, v_inst_1744_, v_inst_1745_, v_u_1753_, v_type_1752_, v_semiringInst_1754_);
v___x_1756_ = lean_apply_4(v_toBind_1746_, lean_box(0), lean_box(0), v___x_1755_, v___f_1747_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_inst_1760_){
_start:
{
lean_object* v_toApplicative_1761_; lean_object* v_toBind_1762_; lean_object* v_getRing_1763_; lean_object* v_modifyRing_1764_; lean_object* v_toPure_1765_; lean_object* v___f_1766_; lean_object* v___f_1767_; lean_object* v___x_1768_; 
v_toApplicative_1761_ = lean_ctor_get(v_inst_1758_, 0);
v_toBind_1762_ = lean_ctor_get(v_inst_1758_, 1);
lean_inc_n(v_toBind_1762_, 3);
v_getRing_1763_ = lean_ctor_get(v_inst_1760_, 0);
lean_inc(v_getRing_1763_);
v_modifyRing_1764_ = lean_ctor_get(v_inst_1760_, 1);
lean_inc(v_modifyRing_1764_);
lean_dec_ref(v_inst_1760_);
v_toPure_1765_ = lean_ctor_get(v_toApplicative_1761_, 1);
lean_inc_n(v_toPure_1765_, 2);
v___f_1766_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1766_, 0, v_toPure_1765_);
lean_closure_set(v___f_1766_, 1, v_modifyRing_1764_);
lean_closure_set(v___f_1766_, 2, v_toBind_1762_);
v___f_1767_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1767_, 0, v_toPure_1765_);
lean_closure_set(v___f_1767_, 1, v_inst_1757_);
lean_closure_set(v___f_1767_, 2, v_inst_1758_);
lean_closure_set(v___f_1767_, 3, v_inst_1759_);
lean_closure_set(v___f_1767_, 4, v_toBind_1762_);
lean_closure_set(v___f_1767_, 5, v___f_1766_);
v___x_1768_ = lean_apply_4(v_toBind_1762_, lean_box(0), lean_box(0), v_getRing_1763_, v___f_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object* v_m_1769_, lean_object* v_inst_1770_, lean_object* v_inst_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_1770_, v_inst_1771_, v_inst_1772_, v_inst_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object* v_invFn_1775_, lean_object* v_s_1776_){
_start:
{
lean_object* v_toRing_1777_; lean_object* v_divFn_x3f_1778_; lean_object* v_semiringId_x3f_1779_; lean_object* v_commSemiringInst_1780_; lean_object* v_commRingInst_1781_; lean_object* v_noZeroDivInst_x3f_1782_; lean_object* v_fieldInst_x3f_1783_; lean_object* v_powIdentityInst_x3f_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1792_; 
v_toRing_1777_ = lean_ctor_get(v_s_1776_, 0);
v_divFn_x3f_1778_ = lean_ctor_get(v_s_1776_, 2);
v_semiringId_x3f_1779_ = lean_ctor_get(v_s_1776_, 3);
v_commSemiringInst_1780_ = lean_ctor_get(v_s_1776_, 4);
v_commRingInst_1781_ = lean_ctor_get(v_s_1776_, 5);
v_noZeroDivInst_x3f_1782_ = lean_ctor_get(v_s_1776_, 6);
v_fieldInst_x3f_1783_ = lean_ctor_get(v_s_1776_, 7);
v_powIdentityInst_x3f_1784_ = lean_ctor_get(v_s_1776_, 8);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_s_1776_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v_s_1776_, 1);
lean_dec(v_unused_1793_);
v___x_1786_ = v_s_1776_;
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1784_);
lean_inc(v_fieldInst_x3f_1783_);
lean_inc(v_noZeroDivInst_x3f_1782_);
lean_inc(v_commRingInst_1781_);
lean_inc(v_commSemiringInst_1780_);
lean_inc(v_semiringId_x3f_1779_);
lean_inc(v_divFn_x3f_1778_);
lean_inc(v_toRing_1777_);
lean_dec(v_s_1776_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_invFn_1775_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 1, v___x_1788_);
v___x_1790_ = v___x_1786_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_toRing_1777_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_divFn_x3f_1778_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v_semiringId_x3f_1779_);
lean_ctor_set(v_reuseFailAlloc_1791_, 4, v_commSemiringInst_1780_);
lean_ctor_set(v_reuseFailAlloc_1791_, 5, v_commRingInst_1781_);
lean_ctor_set(v_reuseFailAlloc_1791_, 6, v_noZeroDivInst_x3f_1782_);
lean_ctor_set(v_reuseFailAlloc_1791_, 7, v_fieldInst_x3f_1783_);
lean_ctor_set(v_reuseFailAlloc_1791_, 8, v_powIdentityInst_x3f_1784_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object* v_toPure_1794_, lean_object* v_invFn_1795_, lean_object* v_____r_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_apply_2(v_toPure_1794_, lean_box(0), v_invFn_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object* v_toPure_1798_, lean_object* v_modifyCommRing_1799_, lean_object* v_toBind_1800_, lean_object* v_invFn_1801_){
_start:
{
lean_object* v___f_1802_; lean_object* v___f_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_inc_ref(v_invFn_1801_);
v___f_1802_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1802_, 0, v_invFn_1801_);
v___f_1803_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1803_, 0, v_toPure_1798_);
lean_closure_set(v___f_1803_, 1, v_invFn_1801_);
v___x_1804_ = lean_apply_1(v_modifyCommRing_1799_, v___f_1802_);
v___x_1805_ = lean_apply_4(v_toBind_1800_, lean_box(0), lean_box(0), v___x_1804_, v___f_1803_);
return v___x_1805_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7));
v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object* v_toPure_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_inst_1827_, lean_object* v_toBind_1828_, lean_object* v___f_1829_, lean_object* v_ring_1830_){
_start:
{
lean_object* v_fieldInst_x3f_1831_; 
v_fieldInst_x3f_1831_ = lean_ctor_get(v_ring_1830_, 7);
if (lean_obj_tag(v_fieldInst_x3f_1831_) == 1)
{
lean_object* v_invFn_x3f_1832_; 
lean_inc_ref(v_fieldInst_x3f_1831_);
v_invFn_x3f_1832_ = lean_ctor_get(v_ring_1830_, 1);
if (lean_obj_tag(v_invFn_x3f_1832_) == 1)
{
lean_object* v_val_1833_; lean_object* v___x_1834_; 
lean_inc_ref(v_invFn_x3f_1832_);
lean_dec_ref_known(v_fieldInst_x3f_1831_, 1);
lean_dec_ref(v_ring_1830_);
lean_dec(v___f_1829_);
lean_dec(v_toBind_1828_);
lean_dec_ref(v_inst_1827_);
lean_dec_ref(v_inst_1826_);
lean_dec_ref(v_inst_1825_);
lean_dec(v_inst_1824_);
v_val_1833_ = lean_ctor_get(v_invFn_x3f_1832_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v_invFn_x3f_1832_, 1);
v___x_1834_ = lean_apply_2(v_toPure_1823_, lean_box(0), v_val_1833_);
return v___x_1834_;
}
else
{
lean_object* v_toRing_1835_; lean_object* v_val_1836_; lean_object* v_type_1837_; lean_object* v_u_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v_expectedInst_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_dec(v_toPure_1823_);
v_toRing_1835_ = lean_ctor_get(v_ring_1830_, 0);
lean_inc_ref(v_toRing_1835_);
lean_dec_ref(v_ring_1830_);
v_val_1836_ = lean_ctor_get(v_fieldInst_x3f_1831_, 0);
lean_inc(v_val_1836_);
lean_dec_ref_known(v_fieldInst_x3f_1831_, 1);
v_type_1837_ = lean_ctor_get(v_toRing_1835_, 1);
lean_inc_ref_n(v_type_1837_, 2);
v_u_1838_ = lean_ctor_get(v_toRing_1835_, 2);
lean_inc_n(v_u_1838_, 2);
lean_dec_ref(v_toRing_1835_);
v___x_1839_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2));
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_u_1838_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l_Lean_mkConst(v___x_1839_, v___x_1841_);
v_expectedInst_1843_ = l_Lean_mkAppB(v___x_1842_, v_type_1837_, v_val_1836_);
v___x_1844_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4));
v___x_1845_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6));
v___x_1846_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1824_, v_inst_1825_, v_inst_1826_, v_inst_1827_, v_type_1837_, v_u_1838_, v___x_1844_, v___x_1845_, v_expectedInst_1843_);
v___x_1847_ = lean_apply_4(v_toBind_1828_, lean_box(0), lean_box(0), v___x_1846_, v___f_1829_);
return v___x_1847_;
}
}
else
{
lean_object* v_toRing_1848_; lean_object* v_type_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec(v___f_1829_);
lean_dec(v_toBind_1828_);
lean_dec_ref(v_inst_1827_);
lean_dec(v_inst_1824_);
lean_dec(v_toPure_1823_);
v_toRing_1848_ = lean_ctor_get(v_ring_1830_, 0);
lean_inc_ref(v_toRing_1848_);
lean_dec_ref(v_ring_1830_);
v_type_1849_ = lean_ctor_get(v_toRing_1848_, 1);
lean_inc_ref(v_type_1849_);
lean_dec_ref(v_toRing_1848_);
v___x_1850_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1851_ = l_Lean_indentExpr(v_type_1849_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Lean_throwError___redArg(v_inst_1826_, v_inst_1825_, v___x_1852_);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_inst_1858_){
_start:
{
lean_object* v_toApplicative_1859_; lean_object* v_toBind_1860_; lean_object* v_getCommRing_1861_; lean_object* v_modifyCommRing_1862_; lean_object* v_toPure_1863_; lean_object* v___f_1864_; lean_object* v___f_1865_; lean_object* v___x_1866_; 
v_toApplicative_1859_ = lean_ctor_get(v_inst_1856_, 0);
v_toBind_1860_ = lean_ctor_get(v_inst_1856_, 1);
lean_inc_n(v_toBind_1860_, 3);
v_getCommRing_1861_ = lean_ctor_get(v_inst_1858_, 0);
lean_inc(v_getCommRing_1861_);
v_modifyCommRing_1862_ = lean_ctor_get(v_inst_1858_, 1);
lean_inc(v_modifyCommRing_1862_);
lean_dec_ref(v_inst_1858_);
v_toPure_1863_ = lean_ctor_get(v_toApplicative_1859_, 1);
lean_inc_n(v_toPure_1863_, 2);
v___f_1864_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1864_, 0, v_toPure_1863_);
lean_closure_set(v___f_1864_, 1, v_modifyCommRing_1862_);
lean_closure_set(v___f_1864_, 2, v_toBind_1860_);
v___f_1865_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1865_, 0, v_toPure_1863_);
lean_closure_set(v___f_1865_, 1, v_inst_1854_);
lean_closure_set(v___f_1865_, 2, v_inst_1855_);
lean_closure_set(v___f_1865_, 3, v_inst_1856_);
lean_closure_set(v___f_1865_, 4, v_inst_1857_);
lean_closure_set(v___f_1865_, 5, v_toBind_1860_);
lean_closure_set(v___f_1865_, 6, v___f_1864_);
v___x_1866_ = lean_apply_4(v_toBind_1860_, lean_box(0), lean_box(0), v_getCommRing_1861_, v___f_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object* v_m_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg(v_inst_1868_, v_inst_1869_, v_inst_1870_, v_inst_1871_, v_inst_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0(lean_object* v_divFn_1874_, lean_object* v_s_1875_){
_start:
{
lean_object* v_toRing_1876_; lean_object* v_invFn_x3f_1877_; lean_object* v_semiringId_x3f_1878_; lean_object* v_commSemiringInst_1879_; lean_object* v_commRingInst_1880_; lean_object* v_noZeroDivInst_x3f_1881_; lean_object* v_fieldInst_x3f_1882_; lean_object* v_powIdentityInst_x3f_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1891_; 
v_toRing_1876_ = lean_ctor_get(v_s_1875_, 0);
v_invFn_x3f_1877_ = lean_ctor_get(v_s_1875_, 1);
v_semiringId_x3f_1878_ = lean_ctor_get(v_s_1875_, 3);
v_commSemiringInst_1879_ = lean_ctor_get(v_s_1875_, 4);
v_commRingInst_1880_ = lean_ctor_get(v_s_1875_, 5);
v_noZeroDivInst_x3f_1881_ = lean_ctor_get(v_s_1875_, 6);
v_fieldInst_x3f_1882_ = lean_ctor_get(v_s_1875_, 7);
v_powIdentityInst_x3f_1883_ = lean_ctor_get(v_s_1875_, 8);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_s_1875_);
if (v_isSharedCheck_1891_ == 0)
{
lean_object* v_unused_1892_; 
v_unused_1892_ = lean_ctor_get(v_s_1875_, 2);
lean_dec(v_unused_1892_);
v___x_1885_ = v_s_1875_;
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1883_);
lean_inc(v_fieldInst_x3f_1882_);
lean_inc(v_noZeroDivInst_x3f_1881_);
lean_inc(v_commRingInst_1880_);
lean_inc(v_commSemiringInst_1879_);
lean_inc(v_semiringId_x3f_1878_);
lean_inc(v_invFn_x3f_1877_);
lean_inc(v_toRing_1876_);
lean_dec(v_s_1875_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_divFn_1874_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 2, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_toRing_1876_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_invFn_x3f_1877_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_semiringId_x3f_1878_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_commSemiringInst_1879_);
lean_ctor_set(v_reuseFailAlloc_1890_, 5, v_commRingInst_1880_);
lean_ctor_set(v_reuseFailAlloc_1890_, 6, v_noZeroDivInst_x3f_1881_);
lean_ctor_set(v_reuseFailAlloc_1890_, 7, v_fieldInst_x3f_1882_);
lean_ctor_set(v_reuseFailAlloc_1890_, 8, v_powIdentityInst_x3f_1883_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1(lean_object* v_toPure_1893_, lean_object* v_divFn_1894_, lean_object* v_____r_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_apply_2(v_toPure_1893_, lean_box(0), v_divFn_1894_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2(lean_object* v_toPure_1897_, lean_object* v_modifyCommRing_1898_, lean_object* v_toBind_1899_, lean_object* v_divFn_1900_){
_start:
{
lean_object* v___f_1901_; lean_object* v___f_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_inc_ref(v_divFn_1900_);
v___f_1901_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1901_, 0, v_divFn_1900_);
v___f_1902_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1902_, 0, v_toPure_1897_);
lean_closure_set(v___f_1902_, 1, v_divFn_1900_);
v___x_1903_ = lean_apply_1(v_modifyCommRing_1898_, v___f_1901_);
v___x_1904_ = lean_apply_4(v_toBind_1899_, lean_box(0), lean_box(0), v___x_1903_, v___f_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3(lean_object* v_toPure_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_toBind_1926_, lean_object* v___f_1927_, lean_object* v_ring_1928_){
_start:
{
lean_object* v_fieldInst_x3f_1929_; 
v_fieldInst_x3f_1929_ = lean_ctor_get(v_ring_1928_, 7);
if (lean_obj_tag(v_fieldInst_x3f_1929_) == 1)
{
lean_object* v_divFn_x3f_1930_; 
lean_inc_ref(v_fieldInst_x3f_1929_);
v_divFn_x3f_1930_ = lean_ctor_get(v_ring_1928_, 2);
if (lean_obj_tag(v_divFn_x3f_1930_) == 1)
{
lean_object* v_val_1931_; lean_object* v___x_1932_; 
lean_inc_ref(v_divFn_x3f_1930_);
lean_dec_ref_known(v_fieldInst_x3f_1929_, 1);
lean_dec_ref(v_ring_1928_);
lean_dec(v___f_1927_);
lean_dec(v_toBind_1926_);
lean_dec_ref(v_inst_1925_);
lean_dec_ref(v_inst_1924_);
lean_dec_ref(v_inst_1923_);
lean_dec(v_inst_1922_);
v_val_1931_ = lean_ctor_get(v_divFn_x3f_1930_, 0);
lean_inc(v_val_1931_);
lean_dec_ref_known(v_divFn_x3f_1930_, 1);
v___x_1932_ = lean_apply_2(v_toPure_1921_, lean_box(0), v_val_1931_);
return v___x_1932_;
}
else
{
lean_object* v_toRing_1933_; lean_object* v_val_1934_; lean_object* v_type_1935_; lean_object* v_u_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v_expectedInst_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
lean_dec(v_toPure_1921_);
v_toRing_1933_ = lean_ctor_get(v_ring_1928_, 0);
lean_inc_ref(v_toRing_1933_);
lean_dec_ref(v_ring_1928_);
v_val_1934_ = lean_ctor_get(v_fieldInst_x3f_1929_, 0);
lean_inc(v_val_1934_);
lean_dec_ref_known(v_fieldInst_x3f_1929_, 1);
v_type_1935_ = lean_ctor_get(v_toRing_1933_, 1);
lean_inc_ref_n(v_type_1935_, 3);
v_u_1936_ = lean_ctor_get(v_toRing_1933_, 2);
lean_inc_n(v_u_1936_, 2);
lean_dec_ref(v_toRing_1933_);
v___x_1937_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__1));
v___x_1938_ = lean_box(0);
v___x_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1939_, 0, v_u_1936_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
lean_inc_ref(v___x_1939_);
v___x_1940_ = l_Lean_mkConst(v___x_1937_, v___x_1939_);
v___x_1941_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__3));
v___x_1942_ = l_Lean_mkConst(v___x_1941_, v___x_1939_);
v___x_1943_ = l_Lean_mkAppB(v___x_1942_, v_type_1935_, v_val_1934_);
v_expectedInst_1944_ = l_Lean_mkAppB(v___x_1940_, v_type_1935_, v___x_1943_);
v___x_1945_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__5));
v___x_1946_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3___closed__7));
v___x_1947_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1922_, v_inst_1923_, v_inst_1924_, v_inst_1925_, v_type_1935_, v_u_1936_, v___x_1945_, v___x_1946_, v_expectedInst_1944_);
v___x_1948_ = lean_apply_4(v_toBind_1926_, lean_box(0), lean_box(0), v___x_1947_, v___f_1927_);
return v___x_1948_;
}
}
else
{
lean_object* v_toRing_1949_; lean_object* v_type_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec(v___f_1927_);
lean_dec(v_toBind_1926_);
lean_dec_ref(v_inst_1925_);
lean_dec(v_inst_1922_);
lean_dec(v_toPure_1921_);
v_toRing_1949_ = lean_ctor_get(v_ring_1928_, 0);
lean_inc_ref(v_toRing_1949_);
lean_dec_ref(v_ring_1928_);
v_type_1950_ = lean_ctor_get(v_toRing_1949_, 1);
lean_inc_ref(v_type_1950_);
lean_dec_ref(v_toRing_1949_);
v___x_1951_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1952_ = l_Lean_indentExpr(v_type_1950_);
v___x_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = l_Lean_throwError___redArg(v_inst_1924_, v_inst_1923_, v___x_1953_);
return v___x_1954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn___redArg(lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_){
_start:
{
lean_object* v_toApplicative_1960_; lean_object* v_toBind_1961_; lean_object* v_getCommRing_1962_; lean_object* v_modifyCommRing_1963_; lean_object* v_toPure_1964_; lean_object* v___f_1965_; lean_object* v___f_1966_; lean_object* v___x_1967_; 
v_toApplicative_1960_ = lean_ctor_get(v_inst_1957_, 0);
v_toBind_1961_ = lean_ctor_get(v_inst_1957_, 1);
lean_inc_n(v_toBind_1961_, 3);
v_getCommRing_1962_ = lean_ctor_get(v_inst_1959_, 0);
lean_inc(v_getCommRing_1962_);
v_modifyCommRing_1963_ = lean_ctor_get(v_inst_1959_, 1);
lean_inc(v_modifyCommRing_1963_);
lean_dec_ref(v_inst_1959_);
v_toPure_1964_ = lean_ctor_get(v_toApplicative_1960_, 1);
lean_inc_n(v_toPure_1964_, 2);
v___f_1965_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1965_, 0, v_toPure_1964_);
lean_closure_set(v___f_1965_, 1, v_modifyCommRing_1963_);
lean_closure_set(v___f_1965_, 2, v_toBind_1961_);
v___f_1966_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getDivFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1966_, 0, v_toPure_1964_);
lean_closure_set(v___f_1966_, 1, v_inst_1955_);
lean_closure_set(v___f_1966_, 2, v_inst_1956_);
lean_closure_set(v___f_1966_, 3, v_inst_1957_);
lean_closure_set(v___f_1966_, 4, v_inst_1958_);
lean_closure_set(v___f_1966_, 5, v_toBind_1961_);
lean_closure_set(v___f_1966_, 6, v___f_1965_);
v___x_1967_ = lean_apply_4(v_toBind_1961_, lean_box(0), lean_box(0), v_getCommRing_1962_, v___f_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getDivFn(lean_object* v_m_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_Meta_Sym_Arith_getDivFn___redArg(v_inst_1969_, v_inst_1970_, v_inst_1971_, v_inst_1972_, v_inst_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0(lean_object* v_fn_1975_, lean_object* v_s_1976_){
_start:
{
lean_object* v_id_1977_; lean_object* v_type_1978_; lean_object* v_u_1979_; lean_object* v_semiringInst_1980_; lean_object* v_charInst_x3f_1981_; uint8_t v_symbolicChar_1982_; lean_object* v_addFn_x3f_1983_; lean_object* v_mulFn_x3f_1984_; lean_object* v_powFn_x3f_1985_; lean_object* v_natCastFn_x3f_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1994_; 
v_id_1977_ = lean_ctor_get(v_s_1976_, 0);
v_type_1978_ = lean_ctor_get(v_s_1976_, 1);
v_u_1979_ = lean_ctor_get(v_s_1976_, 2);
v_semiringInst_1980_ = lean_ctor_get(v_s_1976_, 3);
v_charInst_x3f_1981_ = lean_ctor_get(v_s_1976_, 4);
v_symbolicChar_1982_ = lean_ctor_get_uint8(v_s_1976_, sizeof(void*)*10);
v_addFn_x3f_1983_ = lean_ctor_get(v_s_1976_, 5);
v_mulFn_x3f_1984_ = lean_ctor_get(v_s_1976_, 6);
v_powFn_x3f_1985_ = lean_ctor_get(v_s_1976_, 7);
v_natCastFn_x3f_1986_ = lean_ctor_get(v_s_1976_, 8);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_s_1976_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v_s_1976_, 9);
lean_dec(v_unused_1995_);
v___x_1988_ = v_s_1976_;
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_natCastFn_x3f_1986_);
lean_inc(v_powFn_x3f_1985_);
lean_inc(v_mulFn_x3f_1984_);
lean_inc(v_addFn_x3f_1983_);
lean_inc(v_charInst_x3f_1981_);
lean_inc(v_semiringInst_1980_);
lean_inc(v_u_1979_);
lean_inc(v_type_1978_);
lean_inc(v_id_1977_);
lean_dec(v_s_1976_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v_fn_1975_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 9, v___x_1990_);
v___x_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_id_1977_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_type_1978_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_u_1979_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_semiringInst_1980_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v_charInst_x3f_1981_);
lean_ctor_set(v_reuseFailAlloc_1993_, 5, v_addFn_x3f_1983_);
lean_ctor_set(v_reuseFailAlloc_1993_, 6, v_mulFn_x3f_1984_);
lean_ctor_set(v_reuseFailAlloc_1993_, 7, v_powFn_x3f_1985_);
lean_ctor_set(v_reuseFailAlloc_1993_, 8, v_natCastFn_x3f_1986_);
lean_ctor_set(v_reuseFailAlloc_1993_, 9, v___x_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*10, v_symbolicChar_1982_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2(lean_object* v_toPure_1996_, lean_object* v_modifySemiring_1997_, lean_object* v_toBind_1998_, lean_object* v_fn_1999_){
_start:
{
lean_object* v___f_2000_; lean_object* v___f_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_inc_ref(v_fn_1999_);
v___f_2000_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2000_, 0, v_fn_1999_);
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2001_, 0, v_toPure_1996_);
lean_closure_set(v___f_2001_, 1, v_fn_1999_);
v___x_2002_ = lean_apply_1(v_modifySemiring_1997_, v___f_2000_);
v___x_2003_ = lean_apply_4(v_toBind_1998_, lean_box(0), lean_box(0), v___x_2002_, v___f_2001_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1(lean_object* v_toPure_2004_, lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_toBind_2008_, lean_object* v___f_2009_, lean_object* v_sr_2010_){
_start:
{
lean_object* v_natSMulFn_x3f_2011_; 
v_natSMulFn_x3f_2011_ = lean_ctor_get(v_sr_2010_, 9);
if (lean_obj_tag(v_natSMulFn_x3f_2011_) == 1)
{
lean_object* v_val_2012_; lean_object* v___x_2013_; 
lean_inc_ref(v_natSMulFn_x3f_2011_);
lean_dec_ref(v_sr_2010_);
lean_dec(v___f_2009_);
lean_dec(v_toBind_2008_);
lean_dec_ref(v_inst_2007_);
lean_dec_ref(v_inst_2006_);
lean_dec(v_inst_2005_);
v_val_2012_ = lean_ctor_get(v_natSMulFn_x3f_2011_, 0);
lean_inc(v_val_2012_);
lean_dec_ref_known(v_natSMulFn_x3f_2011_, 1);
v___x_2013_ = lean_apply_2(v_toPure_2004_, lean_box(0), v_val_2012_);
return v___x_2013_;
}
else
{
lean_object* v_type_2014_; lean_object* v_u_2015_; lean_object* v_semiringInst_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_dec(v_toPure_2004_);
v_type_2014_ = lean_ctor_get(v_sr_2010_, 1);
lean_inc_ref_n(v_type_2014_, 2);
v_u_2015_ = lean_ctor_get(v_sr_2010_, 2);
lean_inc_n(v_u_2015_, 2);
v_semiringInst_2016_ = lean_ctor_get(v_sr_2010_, 3);
lean_inc_ref(v_semiringInst_2016_);
lean_dec_ref(v_sr_2010_);
v___x_2017_ = l_Lean_Nat_mkType;
v___x_2018_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNatSMulFn___redArg___lam__3___closed__1));
v___x_2019_ = lean_box(0);
v___x_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2020_, 0, v_u_2015_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = l_Lean_mkConst(v___x_2018_, v___x_2020_);
v___x_2022_ = l_Lean_mkAppB(v___x_2021_, v_type_2014_, v_semiringInst_2016_);
v___x_2023_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkSMulFn___redArg(v_inst_2005_, v_inst_2006_, v_inst_2007_, v_u_2015_, v_type_2014_, v___x_2017_, v___x_2022_);
v___x_2024_ = lean_apply_4(v_toBind_2008_, lean_box(0), lean_box(0), v___x_2023_, v___f_2009_);
return v___x_2024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_){
_start:
{
lean_object* v_toApplicative_2029_; lean_object* v_toBind_2030_; lean_object* v_getSemiring_2031_; lean_object* v_modifySemiring_2032_; lean_object* v_toPure_2033_; lean_object* v___f_2034_; lean_object* v___f_2035_; lean_object* v___x_2036_; 
v_toApplicative_2029_ = lean_ctor_get(v_inst_2026_, 0);
v_toBind_2030_ = lean_ctor_get(v_inst_2026_, 1);
lean_inc_n(v_toBind_2030_, 3);
v_getSemiring_2031_ = lean_ctor_get(v_inst_2028_, 0);
lean_inc(v_getSemiring_2031_);
v_modifySemiring_2032_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc(v_modifySemiring_2032_);
lean_dec_ref(v_inst_2028_);
v_toPure_2033_ = lean_ctor_get(v_toApplicative_2029_, 1);
lean_inc_n(v_toPure_2033_, 2);
v___f_2034_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2034_, 0, v_toPure_2033_);
lean_closure_set(v___f_2034_, 1, v_modifySemiring_2032_);
lean_closure_set(v___f_2034_, 2, v_toBind_2030_);
v___f_2035_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2035_, 0, v_toPure_2033_);
lean_closure_set(v___f_2035_, 1, v_inst_2025_);
lean_closure_set(v___f_2035_, 2, v_inst_2026_);
lean_closure_set(v___f_2035_, 3, v_inst_2027_);
lean_closure_set(v___f_2035_, 4, v_toBind_2030_);
lean_closure_set(v___f_2035_, 5, v___f_2034_);
v___x_2036_ = lean_apply_4(v_toBind_2030_, lean_box(0), lean_box(0), v_getSemiring_2031_, v___f_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatSMulFn_x27(lean_object* v_m_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_inst_2041_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_Meta_Sym_Arith_getNatSMulFn_x27___redArg(v_inst_2038_, v_inst_2039_, v_inst_2040_, v_inst_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_2043_, lean_object* v_s_2044_){
_start:
{
lean_object* v_id_2045_; lean_object* v_type_2046_; lean_object* v_u_2047_; lean_object* v_semiringInst_2048_; lean_object* v_charInst_x3f_2049_; uint8_t v_symbolicChar_2050_; lean_object* v_mulFn_x3f_2051_; lean_object* v_powFn_x3f_2052_; lean_object* v_natCastFn_x3f_2053_; lean_object* v_natSMulFn_x3f_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2062_; 
v_id_2045_ = lean_ctor_get(v_s_2044_, 0);
v_type_2046_ = lean_ctor_get(v_s_2044_, 1);
v_u_2047_ = lean_ctor_get(v_s_2044_, 2);
v_semiringInst_2048_ = lean_ctor_get(v_s_2044_, 3);
v_charInst_x3f_2049_ = lean_ctor_get(v_s_2044_, 4);
v_symbolicChar_2050_ = lean_ctor_get_uint8(v_s_2044_, sizeof(void*)*10);
v_mulFn_x3f_2051_ = lean_ctor_get(v_s_2044_, 6);
v_powFn_x3f_2052_ = lean_ctor_get(v_s_2044_, 7);
v_natCastFn_x3f_2053_ = lean_ctor_get(v_s_2044_, 8);
v_natSMulFn_x3f_2054_ = lean_ctor_get(v_s_2044_, 9);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_s_2044_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v_s_2044_, 5);
lean_dec(v_unused_2063_);
v___x_2056_ = v_s_2044_;
v_isShared_2057_ = v_isSharedCheck_2062_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_natSMulFn_x3f_2054_);
lean_inc(v_natCastFn_x3f_2053_);
lean_inc(v_powFn_x3f_2052_);
lean_inc(v_mulFn_x3f_2051_);
lean_inc(v_charInst_x3f_2049_);
lean_inc(v_semiringInst_2048_);
lean_inc(v_u_2047_);
lean_inc(v_type_2046_);
lean_inc(v_id_2045_);
lean_dec(v_s_2044_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2062_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_addFn_2043_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 5, v___x_2058_);
v___x_2060_ = v___x_2056_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_id_2045_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_type_2046_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_u_2047_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_semiringInst_2048_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v_charInst_x3f_2049_);
lean_ctor_set(v_reuseFailAlloc_2061_, 5, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2061_, 6, v_mulFn_x3f_2051_);
lean_ctor_set(v_reuseFailAlloc_2061_, 7, v_powFn_x3f_2052_);
lean_ctor_set(v_reuseFailAlloc_2061_, 8, v_natCastFn_x3f_2053_);
lean_ctor_set(v_reuseFailAlloc_2061_, 9, v_natSMulFn_x3f_2054_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, sizeof(void*)*10, v_symbolicChar_2050_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_2064_, lean_object* v_modifySemiring_2065_, lean_object* v_toBind_2066_, lean_object* v_addFn_2067_){
_start:
{
lean_object* v___f_2068_; lean_object* v___f_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_inc_ref(v_addFn_2067_);
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2068_, 0, v_addFn_2067_);
v___f_2069_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2069_, 0, v_toPure_2064_);
lean_closure_set(v___f_2069_, 1, v_addFn_2067_);
v___x_2070_ = lean_apply_1(v_modifySemiring_2065_, v___f_2068_);
v___x_2071_ = lean_apply_4(v_toBind_2066_, lean_box(0), lean_box(0), v___x_2070_, v___f_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_2072_, lean_object* v_inst_2073_, lean_object* v_inst_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_toBind_2077_, lean_object* v___f_2078_, lean_object* v_sr_2079_){
_start:
{
lean_object* v_addFn_x3f_2080_; 
v_addFn_x3f_2080_ = lean_ctor_get(v_sr_2079_, 5);
if (lean_obj_tag(v_addFn_x3f_2080_) == 1)
{
lean_object* v_val_2081_; lean_object* v___x_2082_; 
lean_inc_ref(v_addFn_x3f_2080_);
lean_dec_ref(v_sr_2079_);
lean_dec(v___f_2078_);
lean_dec(v_toBind_2077_);
lean_dec_ref(v_inst_2076_);
lean_dec_ref(v_inst_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec(v_inst_2073_);
v_val_2081_ = lean_ctor_get(v_addFn_x3f_2080_, 0);
lean_inc(v_val_2081_);
lean_dec_ref_known(v_addFn_x3f_2080_, 1);
v___x_2082_ = lean_apply_2(v_toPure_2072_, lean_box(0), v_val_2081_);
return v___x_2082_;
}
else
{
lean_object* v_type_2083_; lean_object* v_u_2084_; lean_object* v_semiringInst_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v_expectedInst_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec(v_toPure_2072_);
v_type_2083_ = lean_ctor_get(v_sr_2079_, 1);
lean_inc_ref_n(v_type_2083_, 3);
v_u_2084_ = lean_ctor_get(v_sr_2079_, 2);
lean_inc_n(v_u_2084_, 2);
v_semiringInst_2085_ = lean_ctor_get(v_sr_2079_, 3);
lean_inc_ref(v_semiringInst_2085_);
lean_dec_ref(v_sr_2079_);
v___x_2086_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_2087_ = lean_box(0);
v___x_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_u_2084_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
lean_inc_ref(v___x_2088_);
v___x_2089_ = l_Lean_mkConst(v___x_2086_, v___x_2088_);
v___x_2090_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_2091_ = l_Lean_mkConst(v___x_2090_, v___x_2088_);
v___x_2092_ = l_Lean_mkAppB(v___x_2091_, v_type_2083_, v_semiringInst_2085_);
v_expectedInst_2093_ = l_Lean_mkAppB(v___x_2089_, v_type_2083_, v___x_2092_);
v___x_2094_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_2095_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_2096_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_2073_, v_inst_2074_, v_inst_2075_, v_inst_2076_, v_type_2083_, v_u_2084_, v___x_2094_, v___x_2095_, v_expectedInst_2093_);
v___x_2097_ = lean_apply_4(v_toBind_2077_, lean_box(0), lean_box(0), v___x_2096_, v___f_2078_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_){
_start:
{
lean_object* v_toApplicative_2103_; lean_object* v_toBind_2104_; lean_object* v_getSemiring_2105_; lean_object* v_modifySemiring_2106_; lean_object* v_toPure_2107_; lean_object* v___f_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; 
v_toApplicative_2103_ = lean_ctor_get(v_inst_2100_, 0);
v_toBind_2104_ = lean_ctor_get(v_inst_2100_, 1);
lean_inc_n(v_toBind_2104_, 3);
v_getSemiring_2105_ = lean_ctor_get(v_inst_2102_, 0);
lean_inc(v_getSemiring_2105_);
v_modifySemiring_2106_ = lean_ctor_get(v_inst_2102_, 1);
lean_inc(v_modifySemiring_2106_);
lean_dec_ref(v_inst_2102_);
v_toPure_2107_ = lean_ctor_get(v_toApplicative_2103_, 1);
lean_inc_n(v_toPure_2107_, 2);
v___f_2108_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2108_, 0, v_toPure_2107_);
lean_closure_set(v___f_2108_, 1, v_modifySemiring_2106_);
lean_closure_set(v___f_2108_, 2, v_toBind_2104_);
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_2109_, 0, v_toPure_2107_);
lean_closure_set(v___f_2109_, 1, v_inst_2098_);
lean_closure_set(v___f_2109_, 2, v_inst_2099_);
lean_closure_set(v___f_2109_, 3, v_inst_2100_);
lean_closure_set(v___f_2109_, 4, v_inst_2101_);
lean_closure_set(v___f_2109_, 5, v_toBind_2104_);
lean_closure_set(v___f_2109_, 6, v___f_2108_);
v___x_2110_ = lean_apply_4(v_toBind_2104_, lean_box(0), lean_box(0), v_getSemiring_2105_, v___f_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object* v_m_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_2112_, v_inst_2113_, v_inst_2114_, v_inst_2115_, v_inst_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_2118_, lean_object* v_s_2119_){
_start:
{
lean_object* v_id_2120_; lean_object* v_type_2121_; lean_object* v_u_2122_; lean_object* v_semiringInst_2123_; lean_object* v_charInst_x3f_2124_; uint8_t v_symbolicChar_2125_; lean_object* v_addFn_x3f_2126_; lean_object* v_powFn_x3f_2127_; lean_object* v_natCastFn_x3f_2128_; lean_object* v_natSMulFn_x3f_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2137_; 
v_id_2120_ = lean_ctor_get(v_s_2119_, 0);
v_type_2121_ = lean_ctor_get(v_s_2119_, 1);
v_u_2122_ = lean_ctor_get(v_s_2119_, 2);
v_semiringInst_2123_ = lean_ctor_get(v_s_2119_, 3);
v_charInst_x3f_2124_ = lean_ctor_get(v_s_2119_, 4);
v_symbolicChar_2125_ = lean_ctor_get_uint8(v_s_2119_, sizeof(void*)*10);
v_addFn_x3f_2126_ = lean_ctor_get(v_s_2119_, 5);
v_powFn_x3f_2127_ = lean_ctor_get(v_s_2119_, 7);
v_natCastFn_x3f_2128_ = lean_ctor_get(v_s_2119_, 8);
v_natSMulFn_x3f_2129_ = lean_ctor_get(v_s_2119_, 9);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_s_2119_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v_s_2119_, 6);
lean_dec(v_unused_2138_);
v___x_2131_ = v_s_2119_;
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_natSMulFn_x3f_2129_);
lean_inc(v_natCastFn_x3f_2128_);
lean_inc(v_powFn_x3f_2127_);
lean_inc(v_addFn_x3f_2126_);
lean_inc(v_charInst_x3f_2124_);
lean_inc(v_semiringInst_2123_);
lean_inc(v_u_2122_);
lean_inc(v_type_2121_);
lean_inc(v_id_2120_);
lean_dec(v_s_2119_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2137_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_mulFn_2118_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 6, v___x_2133_);
v___x_2135_ = v___x_2131_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_id_2120_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_type_2121_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_u_2122_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_semiringInst_2123_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_charInst_x3f_2124_);
lean_ctor_set(v_reuseFailAlloc_2136_, 5, v_addFn_x3f_2126_);
lean_ctor_set(v_reuseFailAlloc_2136_, 6, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2136_, 7, v_powFn_x3f_2127_);
lean_ctor_set(v_reuseFailAlloc_2136_, 8, v_natCastFn_x3f_2128_);
lean_ctor_set(v_reuseFailAlloc_2136_, 9, v_natSMulFn_x3f_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10, v_symbolicChar_2125_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_2139_, lean_object* v_modifySemiring_2140_, lean_object* v_toBind_2141_, lean_object* v_mulFn_2142_){
_start:
{
lean_object* v___f_2143_; lean_object* v___f_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_inc_ref(v_mulFn_2142_);
v___f_2143_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2143_, 0, v_mulFn_2142_);
v___f_2144_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2144_, 0, v_toPure_2139_);
lean_closure_set(v___f_2144_, 1, v_mulFn_2142_);
v___x_2145_ = lean_apply_1(v_modifySemiring_2140_, v___f_2143_);
v___x_2146_ = lean_apply_4(v_toBind_2141_, lean_box(0), lean_box(0), v___x_2145_, v___f_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_inst_2150_, lean_object* v_inst_2151_, lean_object* v_toBind_2152_, lean_object* v___f_2153_, lean_object* v_sr_2154_){
_start:
{
lean_object* v_mulFn_x3f_2155_; 
v_mulFn_x3f_2155_ = lean_ctor_get(v_sr_2154_, 6);
if (lean_obj_tag(v_mulFn_x3f_2155_) == 1)
{
lean_object* v_val_2156_; lean_object* v___x_2157_; 
lean_inc_ref(v_mulFn_x3f_2155_);
lean_dec_ref(v_sr_2154_);
lean_dec(v___f_2153_);
lean_dec(v_toBind_2152_);
lean_dec_ref(v_inst_2151_);
lean_dec_ref(v_inst_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec(v_inst_2148_);
v_val_2156_ = lean_ctor_get(v_mulFn_x3f_2155_, 0);
lean_inc(v_val_2156_);
lean_dec_ref_known(v_mulFn_x3f_2155_, 1);
v___x_2157_ = lean_apply_2(v_toPure_2147_, lean_box(0), v_val_2156_);
return v___x_2157_;
}
else
{
lean_object* v_type_2158_; lean_object* v_u_2159_; lean_object* v_semiringInst_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_expectedInst_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec(v_toPure_2147_);
v_type_2158_ = lean_ctor_get(v_sr_2154_, 1);
lean_inc_ref_n(v_type_2158_, 3);
v_u_2159_ = lean_ctor_get(v_sr_2154_, 2);
lean_inc_n(v_u_2159_, 2);
v_semiringInst_2160_ = lean_ctor_get(v_sr_2154_, 3);
lean_inc_ref(v_semiringInst_2160_);
lean_dec_ref(v_sr_2154_);
v___x_2161_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_2162_ = lean_box(0);
v___x_2163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2163_, 0, v_u_2159_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
lean_inc_ref(v___x_2163_);
v___x_2164_ = l_Lean_mkConst(v___x_2161_, v___x_2163_);
v___x_2165_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_2166_ = l_Lean_mkConst(v___x_2165_, v___x_2163_);
v___x_2167_ = l_Lean_mkAppB(v___x_2166_, v_type_2158_, v_semiringInst_2160_);
v_expectedInst_2168_ = l_Lean_mkAppB(v___x_2164_, v_type_2158_, v___x_2167_);
v___x_2169_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_2170_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_2171_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_2148_, v_inst_2149_, v_inst_2150_, v_inst_2151_, v_type_2158_, v_u_2159_, v___x_2169_, v___x_2170_, v_expectedInst_2168_);
v___x_2172_ = lean_apply_4(v_toBind_2152_, lean_box(0), lean_box(0), v___x_2171_, v___f_2153_);
return v___x_2172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_){
_start:
{
lean_object* v_toApplicative_2178_; lean_object* v_toBind_2179_; lean_object* v_getSemiring_2180_; lean_object* v_modifySemiring_2181_; lean_object* v_toPure_2182_; lean_object* v___f_2183_; lean_object* v___f_2184_; lean_object* v___x_2185_; 
v_toApplicative_2178_ = lean_ctor_get(v_inst_2175_, 0);
v_toBind_2179_ = lean_ctor_get(v_inst_2175_, 1);
lean_inc_n(v_toBind_2179_, 3);
v_getSemiring_2180_ = lean_ctor_get(v_inst_2177_, 0);
lean_inc(v_getSemiring_2180_);
v_modifySemiring_2181_ = lean_ctor_get(v_inst_2177_, 1);
lean_inc(v_modifySemiring_2181_);
lean_dec_ref(v_inst_2177_);
v_toPure_2182_ = lean_ctor_get(v_toApplicative_2178_, 1);
lean_inc_n(v_toPure_2182_, 2);
v___f_2183_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2183_, 0, v_toPure_2182_);
lean_closure_set(v___f_2183_, 1, v_modifySemiring_2181_);
lean_closure_set(v___f_2183_, 2, v_toBind_2179_);
v___f_2184_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_2184_, 0, v_toPure_2182_);
lean_closure_set(v___f_2184_, 1, v_inst_2173_);
lean_closure_set(v___f_2184_, 2, v_inst_2174_);
lean_closure_set(v___f_2184_, 3, v_inst_2175_);
lean_closure_set(v___f_2184_, 4, v_inst_2176_);
lean_closure_set(v___f_2184_, 5, v_toBind_2179_);
lean_closure_set(v___f_2184_, 6, v___f_2183_);
v___x_2185_ = lean_apply_4(v_toBind_2179_, lean_box(0), lean_box(0), v_getSemiring_2180_, v___f_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object* v_m_2186_, lean_object* v_inst_2187_, lean_object* v_inst_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_, lean_object* v_inst_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_2187_, v_inst_2188_, v_inst_2189_, v_inst_2190_, v_inst_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_2193_, lean_object* v_s_2194_){
_start:
{
lean_object* v_id_2195_; lean_object* v_type_2196_; lean_object* v_u_2197_; lean_object* v_semiringInst_2198_; lean_object* v_charInst_x3f_2199_; uint8_t v_symbolicChar_2200_; lean_object* v_addFn_x3f_2201_; lean_object* v_mulFn_x3f_2202_; lean_object* v_natCastFn_x3f_2203_; lean_object* v_natSMulFn_x3f_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2212_; 
v_id_2195_ = lean_ctor_get(v_s_2194_, 0);
v_type_2196_ = lean_ctor_get(v_s_2194_, 1);
v_u_2197_ = lean_ctor_get(v_s_2194_, 2);
v_semiringInst_2198_ = lean_ctor_get(v_s_2194_, 3);
v_charInst_x3f_2199_ = lean_ctor_get(v_s_2194_, 4);
v_symbolicChar_2200_ = lean_ctor_get_uint8(v_s_2194_, sizeof(void*)*10);
v_addFn_x3f_2201_ = lean_ctor_get(v_s_2194_, 5);
v_mulFn_x3f_2202_ = lean_ctor_get(v_s_2194_, 6);
v_natCastFn_x3f_2203_ = lean_ctor_get(v_s_2194_, 8);
v_natSMulFn_x3f_2204_ = lean_ctor_get(v_s_2194_, 9);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_s_2194_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v_s_2194_, 7);
lean_dec(v_unused_2213_);
v___x_2206_ = v_s_2194_;
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_natSMulFn_x3f_2204_);
lean_inc(v_natCastFn_x3f_2203_);
lean_inc(v_mulFn_x3f_2202_);
lean_inc(v_addFn_x3f_2201_);
lean_inc(v_charInst_x3f_2199_);
lean_inc(v_semiringInst_2198_);
lean_inc(v_u_2197_);
lean_inc(v_type_2196_);
lean_inc(v_id_2195_);
lean_dec(v_s_2194_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_powFn_2193_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 7, v___x_2208_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_id_2195_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_type_2196_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_u_2197_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_semiringInst_2198_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_charInst_x3f_2199_);
lean_ctor_set(v_reuseFailAlloc_2211_, 5, v_addFn_x3f_2201_);
lean_ctor_set(v_reuseFailAlloc_2211_, 6, v_mulFn_x3f_2202_);
lean_ctor_set(v_reuseFailAlloc_2211_, 7, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2211_, 8, v_natCastFn_x3f_2203_);
lean_ctor_set(v_reuseFailAlloc_2211_, 9, v_natSMulFn_x3f_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*10, v_symbolicChar_2200_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_2214_, lean_object* v_modifySemiring_2215_, lean_object* v_toBind_2216_, lean_object* v_powFn_2217_){
_start:
{
lean_object* v___f_2218_; lean_object* v___f_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_inc_ref(v_powFn_2217_);
v___f_2218_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2218_, 0, v_powFn_2217_);
v___f_2219_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2219_, 0, v_toPure_2214_);
lean_closure_set(v___f_2219_, 1, v_powFn_2217_);
v___x_2220_ = lean_apply_1(v_modifySemiring_2215_, v___f_2218_);
v___x_2221_ = lean_apply_4(v_toBind_2216_, lean_box(0), lean_box(0), v___x_2220_, v___f_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_inst_2226_, lean_object* v_toBind_2227_, lean_object* v___f_2228_, lean_object* v_sr_2229_){
_start:
{
lean_object* v_powFn_x3f_2230_; 
v_powFn_x3f_2230_ = lean_ctor_get(v_sr_2229_, 7);
if (lean_obj_tag(v_powFn_x3f_2230_) == 1)
{
lean_object* v_val_2231_; lean_object* v___x_2232_; 
lean_inc_ref(v_powFn_x3f_2230_);
lean_dec_ref(v_sr_2229_);
lean_dec(v___f_2228_);
lean_dec(v_toBind_2227_);
lean_dec_ref(v_inst_2226_);
lean_dec_ref(v_inst_2225_);
lean_dec_ref(v_inst_2224_);
lean_dec(v_inst_2223_);
v_val_2231_ = lean_ctor_get(v_powFn_x3f_2230_, 0);
lean_inc(v_val_2231_);
lean_dec_ref_known(v_powFn_x3f_2230_, 1);
v___x_2232_ = lean_apply_2(v_toPure_2222_, lean_box(0), v_val_2231_);
return v___x_2232_;
}
else
{
lean_object* v_type_2233_; lean_object* v_u_2234_; lean_object* v_semiringInst_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec(v_toPure_2222_);
v_type_2233_ = lean_ctor_get(v_sr_2229_, 1);
lean_inc_ref(v_type_2233_);
v_u_2234_ = lean_ctor_get(v_sr_2229_, 2);
lean_inc(v_u_2234_);
v_semiringInst_2235_ = lean_ctor_get(v_sr_2229_, 3);
lean_inc_ref(v_semiringInst_2235_);
lean_dec_ref(v_sr_2229_);
v___x_2236_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_2223_, v_inst_2224_, v_inst_2225_, v_inst_2226_, v_u_2234_, v_type_2233_, v_semiringInst_2235_);
v___x_2237_ = lean_apply_4(v_toBind_2227_, lean_box(0), lean_box(0), v___x_2236_, v___f_2228_);
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_inst_2242_){
_start:
{
lean_object* v_toApplicative_2243_; lean_object* v_toBind_2244_; lean_object* v_getSemiring_2245_; lean_object* v_modifySemiring_2246_; lean_object* v_toPure_2247_; lean_object* v___f_2248_; lean_object* v___f_2249_; lean_object* v___x_2250_; 
v_toApplicative_2243_ = lean_ctor_get(v_inst_2240_, 0);
v_toBind_2244_ = lean_ctor_get(v_inst_2240_, 1);
lean_inc_n(v_toBind_2244_, 3);
v_getSemiring_2245_ = lean_ctor_get(v_inst_2242_, 0);
lean_inc(v_getSemiring_2245_);
v_modifySemiring_2246_ = lean_ctor_get(v_inst_2242_, 1);
lean_inc(v_modifySemiring_2246_);
lean_dec_ref(v_inst_2242_);
v_toPure_2247_ = lean_ctor_get(v_toApplicative_2243_, 1);
lean_inc_n(v_toPure_2247_, 2);
v___f_2248_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2248_, 0, v_toPure_2247_);
lean_closure_set(v___f_2248_, 1, v_modifySemiring_2246_);
lean_closure_set(v___f_2248_, 2, v_toBind_2244_);
v___f_2249_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_2249_, 0, v_toPure_2247_);
lean_closure_set(v___f_2249_, 1, v_inst_2238_);
lean_closure_set(v___f_2249_, 2, v_inst_2239_);
lean_closure_set(v___f_2249_, 3, v_inst_2240_);
lean_closure_set(v___f_2249_, 4, v_inst_2241_);
lean_closure_set(v___f_2249_, 5, v_toBind_2244_);
lean_closure_set(v___f_2249_, 6, v___f_2248_);
v___x_2250_ = lean_apply_4(v_toBind_2244_, lean_box(0), lean_box(0), v_getSemiring_2245_, v___f_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object* v_m_2251_, lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_inst_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_2252_, v_inst_2253_, v_inst_2254_, v_inst_2255_, v_inst_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_2258_, lean_object* v_s_2259_){
_start:
{
lean_object* v_id_2260_; lean_object* v_type_2261_; lean_object* v_u_2262_; lean_object* v_semiringInst_2263_; lean_object* v_charInst_x3f_2264_; uint8_t v_symbolicChar_2265_; lean_object* v_addFn_x3f_2266_; lean_object* v_mulFn_x3f_2267_; lean_object* v_powFn_x3f_2268_; lean_object* v_natSMulFn_x3f_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2277_; 
v_id_2260_ = lean_ctor_get(v_s_2259_, 0);
v_type_2261_ = lean_ctor_get(v_s_2259_, 1);
v_u_2262_ = lean_ctor_get(v_s_2259_, 2);
v_semiringInst_2263_ = lean_ctor_get(v_s_2259_, 3);
v_charInst_x3f_2264_ = lean_ctor_get(v_s_2259_, 4);
v_symbolicChar_2265_ = lean_ctor_get_uint8(v_s_2259_, sizeof(void*)*10);
v_addFn_x3f_2266_ = lean_ctor_get(v_s_2259_, 5);
v_mulFn_x3f_2267_ = lean_ctor_get(v_s_2259_, 6);
v_powFn_x3f_2268_ = lean_ctor_get(v_s_2259_, 7);
v_natSMulFn_x3f_2269_ = lean_ctor_get(v_s_2259_, 9);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_s_2259_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; 
v_unused_2278_ = lean_ctor_get(v_s_2259_, 8);
lean_dec(v_unused_2278_);
v___x_2271_ = v_s_2259_;
v_isShared_2272_ = v_isSharedCheck_2277_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_natSMulFn_x3f_2269_);
lean_inc(v_powFn_x3f_2268_);
lean_inc(v_mulFn_x3f_2267_);
lean_inc(v_addFn_x3f_2266_);
lean_inc(v_charInst_x3f_2264_);
lean_inc(v_semiringInst_2263_);
lean_inc(v_u_2262_);
lean_inc(v_type_2261_);
lean_inc(v_id_2260_);
lean_dec(v_s_2259_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2277_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v_natCastFn_2258_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 8, v___x_2273_);
v___x_2275_ = v___x_2271_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_id_2260_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_type_2261_);
lean_ctor_set(v_reuseFailAlloc_2276_, 2, v_u_2262_);
lean_ctor_set(v_reuseFailAlloc_2276_, 3, v_semiringInst_2263_);
lean_ctor_set(v_reuseFailAlloc_2276_, 4, v_charInst_x3f_2264_);
lean_ctor_set(v_reuseFailAlloc_2276_, 5, v_addFn_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2276_, 6, v_mulFn_x3f_2267_);
lean_ctor_set(v_reuseFailAlloc_2276_, 7, v_powFn_x3f_2268_);
lean_ctor_set(v_reuseFailAlloc_2276_, 8, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2276_, 9, v_natSMulFn_x3f_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*10, v_symbolicChar_2265_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_2279_, lean_object* v_modifySemiring_2280_, lean_object* v_toBind_2281_, lean_object* v_natCastFn_2282_){
_start:
{
lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_inc_ref(v_natCastFn_2282_);
v___f_2283_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2283_, 0, v_natCastFn_2282_);
v___f_2284_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2284_, 0, v_toPure_2279_);
lean_closure_set(v___f_2284_, 1, v_natCastFn_2282_);
v___x_2285_ = lean_apply_1(v_modifySemiring_2280_, v___f_2283_);
v___x_2286_ = lean_apply_4(v_toBind_2281_, lean_box(0), lean_box(0), v___x_2285_, v___f_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_inst_2290_, lean_object* v_toBind_2291_, lean_object* v___f_2292_, lean_object* v_sr_2293_){
_start:
{
lean_object* v_natCastFn_x3f_2294_; 
v_natCastFn_x3f_2294_ = lean_ctor_get(v_sr_2293_, 8);
if (lean_obj_tag(v_natCastFn_x3f_2294_) == 1)
{
lean_object* v_val_2295_; lean_object* v___x_2296_; 
lean_inc_ref(v_natCastFn_x3f_2294_);
lean_dec_ref(v_sr_2293_);
lean_dec(v___f_2292_);
lean_dec(v_toBind_2291_);
lean_dec_ref(v_inst_2290_);
lean_dec_ref(v_inst_2289_);
lean_dec(v_inst_2288_);
v_val_2295_ = lean_ctor_get(v_natCastFn_x3f_2294_, 0);
lean_inc(v_val_2295_);
lean_dec_ref_known(v_natCastFn_x3f_2294_, 1);
v___x_2296_ = lean_apply_2(v_toPure_2287_, lean_box(0), v_val_2295_);
return v___x_2296_;
}
else
{
lean_object* v_type_2297_; lean_object* v_u_2298_; lean_object* v_semiringInst_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec(v_toPure_2287_);
v_type_2297_ = lean_ctor_get(v_sr_2293_, 1);
lean_inc_ref(v_type_2297_);
v_u_2298_ = lean_ctor_get(v_sr_2293_, 2);
lean_inc(v_u_2298_);
v_semiringInst_2299_ = lean_ctor_get(v_sr_2293_, 3);
lean_inc_ref(v_semiringInst_2299_);
lean_dec_ref(v_sr_2293_);
v___x_2300_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_2288_, v_inst_2289_, v_inst_2290_, v_u_2298_, v_type_2297_, v_semiringInst_2299_);
v___x_2301_ = lean_apply_4(v_toBind_2291_, lean_box(0), lean_box(0), v___x_2300_, v___f_2292_);
return v___x_2301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object* v_inst_2302_, lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_){
_start:
{
lean_object* v_toApplicative_2306_; lean_object* v_toBind_2307_; lean_object* v_getSemiring_2308_; lean_object* v_modifySemiring_2309_; lean_object* v_toPure_2310_; lean_object* v___f_2311_; lean_object* v___f_2312_; lean_object* v___x_2313_; 
v_toApplicative_2306_ = lean_ctor_get(v_inst_2303_, 0);
v_toBind_2307_ = lean_ctor_get(v_inst_2303_, 1);
lean_inc_n(v_toBind_2307_, 3);
v_getSemiring_2308_ = lean_ctor_get(v_inst_2305_, 0);
lean_inc(v_getSemiring_2308_);
v_modifySemiring_2309_ = lean_ctor_get(v_inst_2305_, 1);
lean_inc(v_modifySemiring_2309_);
lean_dec_ref(v_inst_2305_);
v_toPure_2310_ = lean_ctor_get(v_toApplicative_2306_, 1);
lean_inc_n(v_toPure_2310_, 2);
v___f_2311_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2311_, 0, v_toPure_2310_);
lean_closure_set(v___f_2311_, 1, v_modifySemiring_2309_);
lean_closure_set(v___f_2311_, 2, v_toBind_2307_);
v___f_2312_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2312_, 0, v_toPure_2310_);
lean_closure_set(v___f_2312_, 1, v_inst_2302_);
lean_closure_set(v___f_2312_, 2, v_inst_2303_);
lean_closure_set(v___f_2312_, 3, v_inst_2304_);
lean_closure_set(v___f_2312_, 4, v_toBind_2307_);
lean_closure_set(v___f_2312_, 5, v___f_2311_);
v___x_2313_ = lean_apply_4(v_toBind_2307_, lean_box(0), lean_box(0), v_getSemiring_2308_, v___f_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object* v_m_2314_, lean_object* v_inst_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_inst_2318_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_2315_, v_inst_2316_, v_inst_2317_, v_inst_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0(lean_object* v_toQFn_2320_, lean_object* v_s_2321_){
_start:
{
lean_object* v_toSemiring_2322_; lean_object* v_ringId_2323_; lean_object* v_commSemiringInst_2324_; lean_object* v_addRightCancelInst_x3f_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2333_; 
v_toSemiring_2322_ = lean_ctor_get(v_s_2321_, 0);
v_ringId_2323_ = lean_ctor_get(v_s_2321_, 1);
v_commSemiringInst_2324_ = lean_ctor_get(v_s_2321_, 2);
v_addRightCancelInst_x3f_2325_ = lean_ctor_get(v_s_2321_, 3);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_s_2321_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v_s_2321_, 4);
lean_dec(v_unused_2334_);
v___x_2327_ = v_s_2321_;
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_2325_);
lean_inc(v_commSemiringInst_2324_);
lean_inc(v_ringId_2323_);
lean_inc(v_toSemiring_2322_);
lean_dec(v_s_2321_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v_toQFn_2320_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 4, v___x_2329_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_toSemiring_2322_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_ringId_2323_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_commSemiringInst_2324_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_addRightCancelInst_x3f_2325_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1(lean_object* v_toPure_2335_, lean_object* v_toQFn_2336_, lean_object* v_____r_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_apply_2(v_toPure_2335_, lean_box(0), v_toQFn_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2(lean_object* v_toPure_2339_, lean_object* v_modifyCommSemiring_2340_, lean_object* v_toBind_2341_, lean_object* v_toQFn_2342_){
_start:
{
lean_object* v___f_2343_; lean_object* v___f_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_inc_ref(v_toQFn_2342_);
v___f_2343_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2343_, 0, v_toQFn_2342_);
v___f_2344_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2344_, 0, v_toPure_2339_);
lean_closure_set(v___f_2344_, 1, v_toQFn_2342_);
v___x_2345_ = lean_apply_1(v_modifyCommSemiring_2340_, v___f_2343_);
v___x_2346_ = lean_apply_4(v_toBind_2341_, lean_box(0), lean_box(0), v___x_2345_, v___f_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3(lean_object* v_toPure_2355_, lean_object* v_inst_2356_, lean_object* v_toBind_2357_, lean_object* v___f_2358_, lean_object* v_s_2359_){
_start:
{
lean_object* v_toQFn_x3f_2360_; 
v_toQFn_x3f_2360_ = lean_ctor_get(v_s_2359_, 4);
if (lean_obj_tag(v_toQFn_x3f_2360_) == 1)
{
lean_object* v_val_2361_; lean_object* v___x_2362_; 
lean_inc_ref(v_toQFn_x3f_2360_);
lean_dec_ref(v_s_2359_);
lean_dec(v___f_2358_);
lean_dec(v_toBind_2357_);
lean_dec_ref(v_inst_2356_);
v_val_2361_ = lean_ctor_get(v_toQFn_x3f_2360_, 0);
lean_inc(v_val_2361_);
lean_dec_ref_known(v_toQFn_x3f_2360_, 1);
v___x_2362_ = lean_apply_2(v_toPure_2355_, lean_box(0), v_val_2361_);
return v___x_2362_;
}
else
{
lean_object* v_toSemiring_2363_; lean_object* v_canonExpr_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_toPure_2355_);
v_toSemiring_2363_ = lean_ctor_get(v_s_2359_, 0);
lean_inc_ref(v_toSemiring_2363_);
lean_dec_ref(v_s_2359_);
v_canonExpr_2364_ = lean_ctor_get(v_inst_2356_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_inst_2356_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; 
v_unused_2381_ = lean_ctor_get(v_inst_2356_, 1);
lean_dec(v_unused_2381_);
v___x_2366_ = v_inst_2356_;
v_isShared_2367_ = v_isSharedCheck_2380_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_canonExpr_2364_);
lean_dec(v_inst_2356_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2380_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_type_2368_; lean_object* v_u_2369_; lean_object* v_semiringInst_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v_type_2368_ = lean_ctor_get(v_toSemiring_2363_, 1);
lean_inc_ref(v_type_2368_);
v_u_2369_ = lean_ctor_get(v_toSemiring_2363_, 2);
lean_inc(v_u_2369_);
v_semiringInst_2370_ = lean_ctor_get(v_toSemiring_2363_, 3);
lean_inc_ref(v_semiringInst_2370_);
lean_dec_ref(v_toSemiring_2363_);
v___x_2371_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3___closed__2));
v___x_2372_ = lean_box(0);
if (v_isShared_2367_ == 0)
{
lean_ctor_set_tag(v___x_2366_, 1);
lean_ctor_set(v___x_2366_, 1, v___x_2372_);
lean_ctor_set(v___x_2366_, 0, v_u_2369_);
v___x_2374_ = v___x_2366_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_u_2369_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2375_ = l_Lean_mkConst(v___x_2371_, v___x_2374_);
v___x_2376_ = l_Lean_mkAppB(v___x_2375_, v_type_2368_, v_semiringInst_2370_);
v___x_2377_ = lean_apply_1(v_canonExpr_2364_, v___x_2376_);
v___x_2378_ = lean_apply_4(v_toBind_2357_, lean_box(0), lean_box(0), v___x_2377_, v___f_2358_);
return v___x_2378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___redArg(lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_){
_start:
{
lean_object* v_toApplicative_2385_; lean_object* v_toBind_2386_; lean_object* v_getCommSemiring_2387_; lean_object* v_modifyCommSemiring_2388_; lean_object* v_toPure_2389_; lean_object* v___f_2390_; lean_object* v___f_2391_; lean_object* v___x_2392_; 
v_toApplicative_2385_ = lean_ctor_get(v_inst_2382_, 0);
lean_inc_ref(v_toApplicative_2385_);
v_toBind_2386_ = lean_ctor_get(v_inst_2382_, 1);
lean_inc_n(v_toBind_2386_, 3);
lean_dec_ref(v_inst_2382_);
v_getCommSemiring_2387_ = lean_ctor_get(v_inst_2384_, 0);
lean_inc(v_getCommSemiring_2387_);
v_modifyCommSemiring_2388_ = lean_ctor_get(v_inst_2384_, 1);
lean_inc(v_modifyCommSemiring_2388_);
lean_dec_ref(v_inst_2384_);
v_toPure_2389_ = lean_ctor_get(v_toApplicative_2385_, 1);
lean_inc_n(v_toPure_2389_, 2);
lean_dec_ref(v_toApplicative_2385_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2390_, 0, v_toPure_2389_);
lean_closure_set(v___f_2390_, 1, v_modifyCommSemiring_2388_);
lean_closure_set(v___f_2390_, 2, v_toBind_2386_);
v___f_2391_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2391_, 0, v_toPure_2389_);
lean_closure_set(v___f_2391_, 1, v_inst_2383_);
lean_closure_set(v___f_2391_, 2, v_toBind_2386_);
lean_closure_set(v___f_2391_, 3, v___f_2390_);
v___x_2392_ = lean_apply_4(v_toBind_2386_, lean_box(0), lean_box(0), v_getCommSemiring_2387_, v___f_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn(lean_object* v_m_2393_, lean_object* v_inst_2394_, lean_object* v_inst_2395_, lean_object* v_inst_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_Meta_Sym_Arith_getToQFn___redArg(v_inst_2394_, v_inst_2395_, v_inst_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0(lean_object* v_addRightCancelInst_x3f_2398_, lean_object* v_s_2399_){
_start:
{
lean_object* v_toSemiring_2400_; lean_object* v_ringId_2401_; lean_object* v_commSemiringInst_2402_; lean_object* v_toQFn_x3f_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2411_; 
v_toSemiring_2400_ = lean_ctor_get(v_s_2399_, 0);
v_ringId_2401_ = lean_ctor_get(v_s_2399_, 1);
v_commSemiringInst_2402_ = lean_ctor_get(v_s_2399_, 2);
v_toQFn_x3f_2403_ = lean_ctor_get(v_s_2399_, 4);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_s_2399_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v_s_2399_, 3);
lean_dec(v_unused_2412_);
v___x_2405_ = v_s_2399_;
v_isShared_2406_ = v_isSharedCheck_2411_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_toQFn_x3f_2403_);
lean_inc(v_commSemiringInst_2402_);
lean_inc(v_ringId_2401_);
lean_inc(v_toSemiring_2400_);
lean_dec(v_s_2399_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2411_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2407_, 0, v_addRightCancelInst_x3f_2398_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 3, v___x_2407_);
v___x_2409_ = v___x_2405_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_toSemiring_2400_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_ringId_2401_);
lean_ctor_set(v_reuseFailAlloc_2410_, 2, v_commSemiringInst_2402_);
lean_ctor_set(v_reuseFailAlloc_2410_, 3, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2410_, 4, v_toQFn_x3f_2403_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1(lean_object* v_toPure_2413_, lean_object* v_addRightCancelInst_x3f_2414_, lean_object* v_____r_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_apply_2(v_toPure_2413_, lean_box(0), v_addRightCancelInst_x3f_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2(lean_object* v_toPure_2417_, lean_object* v_modifyCommSemiring_2418_, lean_object* v_toBind_2419_, lean_object* v_addRightCancelInst_x3f_2420_){
_start:
{
lean_object* v___f_2421_; lean_object* v___f_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_inc(v_addRightCancelInst_x3f_2420_);
v___f_2421_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2421_, 0, v_addRightCancelInst_x3f_2420_);
v___f_2422_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2422_, 0, v_toPure_2417_);
lean_closure_set(v___f_2422_, 1, v_addRightCancelInst_x3f_2420_);
v___x_2423_ = lean_apply_1(v_modifyCommSemiring_2418_, v___f_2421_);
v___x_2424_ = lean_apply_4(v_toBind_2419_, lean_box(0), lean_box(0), v___x_2423_, v___f_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3(lean_object* v___f_2425_, lean_object* v_addRightCancelInst_x3f_2426_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_apply_1(v___f_2425_, v_addRightCancelInst_x3f_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5(lean_object* v___x_2433_, lean_object* v_type_2434_, lean_object* v_synthInstance_x3f_2435_, lean_object* v_toBind_2436_, lean_object* v___f_2437_, lean_object* v_toPure_2438_, lean_object* v___f_2439_, lean_object* v_____x_2440_){
_start:
{
if (lean_obj_tag(v_____x_2440_) == 1)
{
lean_object* v_val_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
lean_dec(v___f_2439_);
lean_dec(v_toPure_2438_);
v_val_2441_ = lean_ctor_get(v_____x_2440_, 0);
lean_inc(v_val_2441_);
lean_dec_ref_known(v_____x_2440_, 1);
v___x_2442_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5___closed__1));
v___x_2443_ = l_Lean_mkConst(v___x_2442_, v___x_2433_);
v___x_2444_ = l_Lean_mkAppB(v___x_2443_, v_type_2434_, v_val_2441_);
v___x_2445_ = lean_apply_1(v_synthInstance_x3f_2435_, v___x_2444_);
v___x_2446_ = lean_apply_4(v_toBind_2436_, lean_box(0), lean_box(0), v___x_2445_, v___f_2437_);
return v___x_2446_;
}
else
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_dec(v_____x_2440_);
lean_dec(v___f_2437_);
lean_dec(v_synthInstance_x3f_2435_);
lean_dec_ref(v_type_2434_);
lean_dec(v___x_2433_);
v___x_2447_ = lean_box(0);
v___x_2448_ = lean_apply_2(v_toPure_2438_, lean_box(0), v___x_2447_);
v___x_2449_ = lean_apply_4(v_toBind_2436_, lean_box(0), lean_box(0), v___x_2448_, v___f_2439_);
return v___x_2449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4(lean_object* v_toPure_2453_, lean_object* v_inst_2454_, lean_object* v_toBind_2455_, lean_object* v___f_2456_, lean_object* v___f_2457_, lean_object* v_s_2458_){
_start:
{
lean_object* v_addRightCancelInst_x3f_2459_; 
v_addRightCancelInst_x3f_2459_ = lean_ctor_get(v_s_2458_, 3);
if (lean_obj_tag(v_addRightCancelInst_x3f_2459_) == 1)
{
lean_object* v_val_2460_; lean_object* v___x_2461_; 
lean_inc_ref(v_addRightCancelInst_x3f_2459_);
lean_dec_ref(v_s_2458_);
lean_dec(v___f_2457_);
lean_dec(v___f_2456_);
lean_dec(v_toBind_2455_);
lean_dec_ref(v_inst_2454_);
v_val_2460_ = lean_ctor_get(v_addRightCancelInst_x3f_2459_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v_addRightCancelInst_x3f_2459_, 1);
v___x_2461_ = lean_apply_2(v_toPure_2453_, lean_box(0), v_val_2460_);
return v___x_2461_;
}
else
{
lean_object* v_toSemiring_2462_; lean_object* v_synthInstance_x3f_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2479_; 
v_toSemiring_2462_ = lean_ctor_get(v_s_2458_, 0);
lean_inc_ref(v_toSemiring_2462_);
lean_dec_ref(v_s_2458_);
v_synthInstance_x3f_2463_ = lean_ctor_get(v_inst_2454_, 1);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_inst_2454_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v_inst_2454_, 0);
lean_dec(v_unused_2480_);
v___x_2465_ = v_inst_2454_;
v_isShared_2466_ = v_isSharedCheck_2479_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_synthInstance_x3f_2463_);
lean_dec(v_inst_2454_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2479_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v_type_2467_; lean_object* v_u_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v_type_2467_ = lean_ctor_get(v_toSemiring_2462_, 1);
lean_inc_ref(v_type_2467_);
v_u_2468_ = lean_ctor_get(v_toSemiring_2462_, 2);
lean_inc(v_u_2468_);
lean_dec_ref(v_toSemiring_2462_);
v___x_2469_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4___closed__1));
v___x_2470_ = lean_box(0);
if (v_isShared_2466_ == 0)
{
lean_ctor_set_tag(v___x_2465_, 1);
lean_ctor_set(v___x_2465_, 1, v___x_2470_);
lean_ctor_set(v___x_2465_, 0, v_u_2468_);
v___x_2472_ = v___x_2465_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_u_2468_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___f_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_inc(v_toBind_2455_);
lean_inc(v_synthInstance_x3f_2463_);
lean_inc_ref(v_type_2467_);
lean_inc_ref(v___x_2472_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_2473_, 0, v___x_2472_);
lean_closure_set(v___f_2473_, 1, v_type_2467_);
lean_closure_set(v___f_2473_, 2, v_synthInstance_x3f_2463_);
lean_closure_set(v___f_2473_, 3, v_toBind_2455_);
lean_closure_set(v___f_2473_, 4, v___f_2456_);
lean_closure_set(v___f_2473_, 5, v_toPure_2453_);
lean_closure_set(v___f_2473_, 6, v___f_2457_);
v___x_2474_ = l_Lean_mkConst(v___x_2469_, v___x_2472_);
v___x_2475_ = l_Lean_Expr_app___override(v___x_2474_, v_type_2467_);
v___x_2476_ = lean_apply_1(v_synthInstance_x3f_2463_, v___x_2475_);
v___x_2477_ = lean_apply_4(v_toBind_2455_, lean_box(0), lean_box(0), v___x_2476_, v___f_2473_);
return v___x_2477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_){
_start:
{
lean_object* v_toApplicative_2484_; lean_object* v_toBind_2485_; lean_object* v_getCommSemiring_2486_; lean_object* v_modifyCommSemiring_2487_; lean_object* v_toPure_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; 
v_toApplicative_2484_ = lean_ctor_get(v_inst_2481_, 0);
lean_inc_ref(v_toApplicative_2484_);
v_toBind_2485_ = lean_ctor_get(v_inst_2481_, 1);
lean_inc_n(v_toBind_2485_, 3);
lean_dec_ref(v_inst_2481_);
v_getCommSemiring_2486_ = lean_ctor_get(v_inst_2483_, 0);
lean_inc(v_getCommSemiring_2486_);
v_modifyCommSemiring_2487_ = lean_ctor_get(v_inst_2483_, 1);
lean_inc(v_modifyCommSemiring_2487_);
lean_dec_ref(v_inst_2483_);
v_toPure_2488_ = lean_ctor_get(v_toApplicative_2484_, 1);
lean_inc_n(v_toPure_2488_, 2);
lean_dec_ref(v_toApplicative_2484_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2489_, 0, v_toPure_2488_);
lean_closure_set(v___f_2489_, 1, v_modifyCommSemiring_2487_);
lean_closure_set(v___f_2489_, 2, v_toBind_2485_);
v___f_2490_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2490_, 0, v___f_2489_);
lean_inc_ref(v___f_2490_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg___lam__4), 6, 5);
lean_closure_set(v___f_2491_, 0, v_toPure_2488_);
lean_closure_set(v___f_2491_, 1, v_inst_2482_);
lean_closure_set(v___f_2491_, 2, v_toBind_2485_);
lean_closure_set(v___f_2491_, 3, v___f_2490_);
lean_closure_set(v___f_2491_, 4, v___f_2490_);
v___x_2492_ = lean_apply_4(v_toBind_2485_, lean_box(0), lean_box(0), v_getCommSemiring_2486_, v___f_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f(lean_object* v_m_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Meta_Sym_Arith_getAddRightCancelInst_x3f___redArg(v_inst_2494_, v_inst_2495_, v_inst_2496_);
return v___x_2497_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Functions_1189967091____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Sym_Arith_checkedInstsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Sym_Arith_checkedInstsExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_MonadRing(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_MonadSemiring(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Functions(builtin);
}
#ifdef __cplusplus
}
#endif
