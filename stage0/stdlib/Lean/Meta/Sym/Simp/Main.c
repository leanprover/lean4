// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Main
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.Simp.Simproc import Lean.Meta.Sym.Simp.App import Lean.Meta.Sym.Simp.Have import Lean.Meta.Sym.Simp.Forall
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
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "unexpected kernel projection term during simplification"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "\npre-process and fold them as projection applications"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "`simp` failed: maximum number of steps exceeded"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2;
LEAN_EXPORT lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(lean_object* v_d_1_, lean_object* v_e_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v_debug_15_; 
v___x_14_ = lean_st_ref_get(v___y_4_);
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*7);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
lean_dec(v___y_8_);
lean_dec_ref(v___y_7_);
lean_dec(v___y_6_);
lean_dec_ref(v___y_5_);
lean_dec_ref(v___y_3_);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
lean_inc(v___y_4_);
lean_inc_ref(v_e_2_);
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_dec_ref(v___x_16_);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
lean_dec(v___y_4_);
lean_dec_ref(v_e_2_);
lean_dec(v_d_1_);
v_a_17_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_16_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_16_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Lean_Expr_mdata___override(v_d_1_, v_e_2_);
v___x_13_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_12_, v___y_11_);
lean_dec(v___y_11_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(lean_object* v_d_25_, lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_25_, v_e_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(lean_object* v_d_35_, lean_object* v_e_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_35_, v_e_36_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(lean_object* v_d_48_, lean_object* v_e_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(v_d_48_, v_e_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(lean_object* v_msgData_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v_env_68_; lean_object* v___x_69_; lean_object* v_mctx_70_; lean_object* v_lctx_71_; lean_object* v_options_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_67_ = lean_st_ref_get(v___y_65_);
v_env_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_env_68_);
lean_dec(v___x_67_);
v___x_69_ = lean_st_ref_get(v___y_63_);
v_mctx_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_mctx_70_);
lean_dec(v___x_69_);
v_lctx_71_ = lean_ctor_get(v___y_62_, 2);
v_options_72_ = lean_ctor_get(v___y_64_, 2);
lean_inc_ref(v_options_72_);
lean_inc_ref(v_lctx_71_);
v___x_73_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_73_, 0, v_env_68_);
lean_ctor_set(v___x_73_, 1, v_mctx_70_);
lean_ctor_set(v___x_73_, 2, v_lctx_71_);
lean_ctor_set(v___x_73_, 3, v_options_72_);
v___x_74_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v_msgData_61_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object* v_msgData_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msgData_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object* v_msg_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_ref_89_; lean_object* v___x_90_; lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_99_; 
v_ref_89_ = lean_ctor_get(v___y_86_, 5);
v___x_90_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
v_a_91_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_99_ == 0)
{
v___x_93_ = v___x_90_;
v_isShared_94_ = v_isSharedCheck_99_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_99_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_97_; 
lean_inc(v_ref_89_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v_ref_89_);
lean_ctor_set(v___x_95_, 1, v_a_91_);
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 1);
lean_ctor_set(v___x_93_, 0, v___x_95_);
v___x_97_ = v___x_93_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object* v_msg_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1));
v___x_111_ = l_Lean_stringToMessageData(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3));
v___x_114_ = l_Lean_stringToMessageData(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object* v_e_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
switch(lean_obj_tag(v_e_115_))
{
case 5:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_Sym_Simp_simpAppArgs(v_e_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
return v___x_126_;
}
case 6:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
return v___x_127_;
}
case 7:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Sym_Simp_simpForall(v_e_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
return v___x_128_;
}
case 8:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
return v___x_129_;
}
case 10:
{
lean_object* v_data_130_; lean_object* v_expr_131_; lean_object* v___x_132_; 
v_data_130_ = lean_ctor_get(v_e_115_, 0);
lean_inc(v_data_130_);
v_expr_131_ = lean_ctor_get(v_e_115_, 1);
lean_inc_ref(v_expr_131_);
lean_dec_ref(v_e_115_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
v___x_132_ = lean_sym_simp(v_expr_131_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_168_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_168_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_168_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_168_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
if (lean_obj_tag(v_a_133_) == 0)
{
lean_object* v___x_137_; lean_object* v___x_139_; 
lean_dec_ref(v_a_133_);
lean_dec(v_data_130_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
v___x_137_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
else
{
lean_object* v_e_x27_141_; lean_object* v_proof_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_167_; 
lean_del_object(v___x_135_);
v_e_x27_141_ = lean_ctor_get(v_a_133_, 0);
v_proof_142_ = lean_ctor_get(v_a_133_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_a_133_);
if (v_isSharedCheck_167_ == 0)
{
v___x_144_ = v_a_133_;
v_isShared_145_ = v_isSharedCheck_167_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_proof_142_);
lean_inc(v_e_x27_141_);
lean_dec(v_a_133_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_167_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_data_130_, v_e_x27_141_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_158_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_158_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_158_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_158_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
uint8_t v___x_151_; lean_object* v___x_153_; 
v___x_151_ = 0;
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v_a_147_);
v___x_153_ = v___x_144_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_147_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_proof_142_);
v___x_153_ = v_reuseFailAlloc_157_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_155_; 
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*2, v___x_151_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_153_);
v___x_155_ = v___x_149_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_del_object(v___x_144_);
lean_dec_ref(v_proof_142_);
v_a_159_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_146_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_146_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
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
}
}
else
{
lean_dec(v_data_130_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
return v___x_132_;
}
}
case 11:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
v___x_169_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2);
v___x_170_ = l_Lean_indentExpr(v_e_115_);
v___x_171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4);
v___x_173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_173_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
return v___x_174_;
}
default: 
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_e_115_);
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0));
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object* v_00_u03b1_189_, lean_object* v_msg_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_190_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object* v_00_u03b1_202_, lean_object* v_msg_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(v_00_u03b1_202_, v_msg_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(lean_object* v_e_217_, lean_object* v_r_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___x_221_; lean_object* v_numSteps_222_; lean_object* v_cache_223_; lean_object* v_funext_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_236_; 
v___x_221_ = lean_st_ref_take(v_a_219_);
v_numSteps_222_ = lean_ctor_get(v___x_221_, 0);
v_cache_223_ = lean_ctor_get(v___x_221_, 1);
v_funext_224_ = lean_ctor_get(v___x_221_, 2);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_236_ == 0)
{
v___x_226_ = v___x_221_;
v_isShared_227_ = v_isSharedCheck_236_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_funext_224_);
lean_inc(v_cache_223_);
lean_inc(v_numSteps_222_);
lean_dec(v___x_221_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_236_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___f_228_; lean_object* v___f_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___f_228_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_229_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
lean_inc_ref(v_r_218_);
v___x_230_ = l_Lean_PersistentHashMap_insert___redArg(v___f_228_, v___f_229_, v_cache_223_, v_e_217_, v_r_218_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_230_);
v___x_232_ = v___x_226_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_numSteps_222_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_funext_224_);
v___x_232_ = v_reuseFailAlloc_235_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_st_ref_set(v_a_219_, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_r_218_);
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(lean_object* v_e_237_, lean_object* v_r_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(v_e_237_, v_r_238_, v_a_239_);
lean_dec(v_a_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(lean_object* v_e_242_, lean_object* v_r_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_254_; lean_object* v_numSteps_255_; lean_object* v_cache_256_; lean_object* v_funext_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_269_; 
v___x_254_ = lean_st_ref_take(v_a_246_);
v_numSteps_255_ = lean_ctor_get(v___x_254_, 0);
v_cache_256_ = lean_ctor_get(v___x_254_, 1);
v_funext_257_ = lean_ctor_get(v___x_254_, 2);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_269_ == 0)
{
v___x_259_ = v___x_254_;
v_isShared_260_ = v_isSharedCheck_269_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_funext_257_);
lean_inc(v_cache_256_);
lean_inc(v_numSteps_255_);
lean_dec(v___x_254_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_269_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___f_261_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0));
v___f_262_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1));
lean_inc_ref(v_r_243_);
v___x_263_ = l_Lean_PersistentHashMap_insert___redArg(v___f_261_, v___f_262_, v_cache_256_, v_e_242_, v_r_243_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v___x_263_);
v___x_265_ = v___x_259_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_numSteps_255_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_funext_257_);
v___x_265_ = v_reuseFailAlloc_268_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_st_ref_set(v_a_246_, v___x_265_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v_r_243_);
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___boxed(lean_object* v_e_270_, lean_object* v_r_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(v_e_270_, v_r_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
return v_res_282_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = l_Lean_maxRecDepthErrorMessage;
v___x_289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3);
v___x_291_ = l_Lean_MessageData_ofFormat(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4);
v___x_293_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2));
v___x_294_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v___x_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object* v_ref_295_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_ref_295_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object* v_ref_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_ref_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object* v_00_u03b1_303_, lean_object* v_ref_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_ref_304_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object* v_00_u03b1_316_, lean_object* v_ref_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(v_00_u03b1_316_, v_ref_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object* v_x_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_post_341_; lean_object* v___x_342_; 
v_post_341_ = lean_ctor_get(v___y_331_, 1);
lean_inc_ref(v_post_341_);
v___x_342_ = lean_apply_11(v_post_341_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, lean_box(0));
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object* v_x_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v_x_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_ks_360_; lean_object* v_vs_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_385_; 
v_ks_360_ = lean_ctor_get(v_x_356_, 0);
v_vs_361_ = lean_ctor_get(v_x_356_, 1);
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_356_);
if (v_isSharedCheck_385_ == 0)
{
v___x_363_ = v_x_356_;
v_isShared_364_ = v_isSharedCheck_385_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_vs_361_);
lean_inc(v_ks_360_);
lean_dec(v_x_356_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_385_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_array_get_size(v_ks_360_);
v___x_366_ = lean_nat_dec_lt(v_x_357_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
lean_dec(v_x_357_);
v___x_367_ = lean_array_push(v_ks_360_, v_x_358_);
v___x_368_ = lean_array_push(v_vs_361_, v_x_359_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 1, v___x_368_);
lean_ctor_set(v___x_363_, 0, v___x_367_);
v___x_370_ = v___x_363_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
else
{
lean_object* v_k_x27_372_; uint8_t v___x_373_; 
v_k_x27_372_ = lean_array_fget_borrowed(v_ks_360_, v_x_357_);
v___x_373_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_358_, v_k_x27_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_375_; 
if (v_isShared_364_ == 0)
{
v___x_375_ = v___x_363_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_ks_360_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_vs_361_);
v___x_375_ = v_reuseFailAlloc_379_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_add(v_x_357_, v___x_376_);
lean_dec(v_x_357_);
v_x_356_ = v___x_375_;
v_x_357_ = v___x_377_;
goto _start;
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_380_ = lean_array_fset(v_ks_360_, v_x_357_, v_x_358_);
v___x_381_ = lean_array_fset(v_vs_361_, v_x_357_, v_x_359_);
lean_dec(v_x_357_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 1, v___x_381_);
lean_ctor_set(v___x_363_, 0, v___x_380_);
v___x_383_ = v___x_363_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_381_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_n_386_, lean_object* v_k_387_, lean_object* v_v_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_n_386_, v___x_389_, v_k_387_, v_v_388_);
return v___x_390_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; 
v___x_391_ = ((size_t)5ULL);
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_shift_left(v___x_392_, v___x_391_);
return v___x_393_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_394_; size_t v___x_395_; size_t v___x_396_; 
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0);
v___x_396_ = lean_usize_sub(v___x_395_, v___x_394_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object* v_x_398_, size_t v_x_399_, size_t v_x_400_, lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v_es_403_; size_t v___x_404_; size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v_j_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_es_403_ = lean_ctor_get(v_x_398_, 0);
v___x_404_ = ((size_t)5ULL);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1);
v___x_407_ = lean_usize_land(v_x_399_, v___x_406_);
v_j_408_ = lean_usize_to_nat(v___x_407_);
v___x_409_ = lean_array_get_size(v_es_403_);
v___x_410_ = lean_nat_dec_lt(v_j_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_dec(v_j_408_);
lean_dec(v_x_402_);
lean_dec_ref(v_x_401_);
return v_x_398_;
}
else
{
lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_447_; 
lean_inc_ref(v_es_403_);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v_x_398_, 0);
lean_dec(v_unused_448_);
v___x_412_ = v_x_398_;
v_isShared_413_ = v_isSharedCheck_447_;
goto v_resetjp_411_;
}
else
{
lean_dec(v_x_398_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_447_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_v_414_; lean_object* v___x_415_; lean_object* v_xs_x27_416_; lean_object* v___y_418_; 
v_v_414_ = lean_array_fget(v_es_403_, v_j_408_);
v___x_415_ = lean_box(0);
v_xs_x27_416_ = lean_array_fset(v_es_403_, v_j_408_, v___x_415_);
switch(lean_obj_tag(v_v_414_))
{
case 0:
{
lean_object* v_key_423_; lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_434_; 
v_key_423_ = lean_ctor_get(v_v_414_, 0);
v_val_424_ = lean_ctor_get(v_v_414_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_v_414_);
if (v_isSharedCheck_434_ == 0)
{
v___x_426_ = v_v_414_;
v_isShared_427_ = v_isSharedCheck_434_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_inc(v_key_423_);
lean_dec(v_v_414_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_434_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___x_428_; 
v___x_428_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_401_, v_key_423_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_del_object(v___x_426_);
v___x_429_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_423_, v_val_424_, v_x_401_, v_x_402_);
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
v___y_418_ = v___x_430_;
goto v___jp_417_;
}
else
{
lean_object* v___x_432_; 
lean_dec(v_val_424_);
lean_dec(v_key_423_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_x_402_);
lean_ctor_set(v___x_426_, 0, v_x_401_);
v___x_432_ = v___x_426_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_x_401_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_x_402_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
v___y_418_ = v___x_432_;
goto v___jp_417_;
}
}
}
}
case 1:
{
lean_object* v_node_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_445_; 
v_node_435_ = lean_ctor_get(v_v_414_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_v_414_);
if (v_isSharedCheck_445_ == 0)
{
v___x_437_ = v_v_414_;
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_node_435_);
lean_dec(v_v_414_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_439_ = lean_usize_shift_right(v_x_399_, v___x_404_);
v___x_440_ = lean_usize_add(v_x_400_, v___x_405_);
v___x_441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_node_435_, v___x_439_, v___x_440_, v_x_401_, v_x_402_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_441_);
v___x_443_ = v___x_437_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
v___y_418_ = v___x_443_;
goto v___jp_417_;
}
}
}
default: 
{
lean_object* v___x_446_; 
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_x_401_);
lean_ctor_set(v___x_446_, 1, v_x_402_);
v___y_418_ = v___x_446_;
goto v___jp_417_;
}
}
v___jp_417_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_array_fset(v_xs_x27_416_, v_j_408_, v___y_418_);
lean_dec(v_j_408_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_419_);
v___x_421_ = v___x_412_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
else
{
lean_object* v_ks_449_; lean_object* v_vs_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_470_; 
v_ks_449_ = lean_ctor_get(v_x_398_, 0);
v_vs_450_ = lean_ctor_get(v_x_398_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_470_ == 0)
{
v___x_452_ = v_x_398_;
v_isShared_453_ = v_isSharedCheck_470_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_vs_450_);
lean_inc(v_ks_449_);
lean_dec(v_x_398_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_470_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_ks_449_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_vs_450_);
v___x_455_ = v_reuseFailAlloc_469_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v_newNode_456_; uint8_t v___y_458_; size_t v___x_464_; uint8_t v___x_465_; 
v_newNode_456_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v___x_455_, v_x_401_, v_x_402_);
v___x_464_ = ((size_t)7ULL);
v___x_465_ = lean_usize_dec_le(v___x_464_, v_x_400_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_466_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_456_);
v___x_467_ = lean_unsigned_to_nat(4u);
v___x_468_ = lean_nat_dec_lt(v___x_466_, v___x_467_);
lean_dec(v___x_466_);
v___y_458_ = v___x_468_;
goto v___jp_457_;
}
else
{
v___y_458_ = v___x_465_;
goto v___jp_457_;
}
v___jp_457_:
{
if (v___y_458_ == 0)
{
lean_object* v_ks_459_; lean_object* v_vs_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_ks_459_ = lean_ctor_get(v_newNode_456_, 0);
lean_inc_ref(v_ks_459_);
v_vs_460_ = lean_ctor_get(v_newNode_456_, 1);
lean_inc_ref(v_vs_460_);
lean_dec_ref(v_newNode_456_);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2);
v___x_463_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_x_400_, v_ks_459_, v_vs_460_, v___x_461_, v___x_462_);
lean_dec_ref(v_vs_460_);
lean_dec_ref(v_ks_459_);
return v___x_463_;
}
else
{
return v_newNode_456_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_471_, lean_object* v_keys_472_, lean_object* v_vals_473_, lean_object* v_i_474_, lean_object* v_entries_475_){
_start:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_array_get_size(v_keys_472_);
v___x_477_ = lean_nat_dec_lt(v_i_474_, v___x_476_);
if (v___x_477_ == 0)
{
lean_dec(v_i_474_);
return v_entries_475_;
}
else
{
lean_object* v_k_478_; lean_object* v_v_479_; uint64_t v___x_480_; size_t v_h_481_; size_t v___x_482_; lean_object* v___x_483_; size_t v___x_484_; size_t v___x_485_; size_t v___x_486_; size_t v_h_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_k_478_ = lean_array_fget_borrowed(v_keys_472_, v_i_474_);
v_v_479_ = lean_array_fget_borrowed(v_vals_473_, v_i_474_);
v___x_480_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_478_);
v_h_481_ = lean_uint64_to_usize(v___x_480_);
v___x_482_ = ((size_t)5ULL);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_sub(v_depth_471_, v___x_484_);
v___x_486_ = lean_usize_mul(v___x_482_, v___x_485_);
v_h_487_ = lean_usize_shift_right(v_h_481_, v___x_486_);
v___x_488_ = lean_nat_add(v_i_474_, v___x_483_);
lean_dec(v_i_474_);
lean_inc(v_v_479_);
lean_inc(v_k_478_);
v___x_489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_entries_475_, v_h_487_, v_depth_471_, v_k_478_, v_v_479_);
v_i_474_ = v___x_488_;
v_entries_475_ = v___x_489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_491_, lean_object* v_keys_492_, lean_object* v_vals_493_, lean_object* v_i_494_, lean_object* v_entries_495_){
_start:
{
size_t v_depth_boxed_496_; lean_object* v_res_497_; 
v_depth_boxed_496_ = lean_unbox_usize(v_depth_491_);
lean_dec(v_depth_491_);
v_res_497_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_496_, v_keys_492_, v_vals_493_, v_i_494_, v_entries_495_);
lean_dec_ref(v_vals_493_);
lean_dec_ref(v_keys_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
size_t v_x_57436__boxed_503_; size_t v_x_57437__boxed_504_; lean_object* v_res_505_; 
v_x_57436__boxed_503_ = lean_unbox_usize(v_x_499_);
lean_dec(v_x_499_);
v_x_57437__boxed_504_ = lean_unbox_usize(v_x_500_);
lean_dec(v_x_500_);
v_res_505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_498_, v_x_57436__boxed_503_, v_x_57437__boxed_504_, v_x_501_, v_x_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
uint64_t v___x_509_; size_t v___x_510_; size_t v___x_511_; lean_object* v___x_512_; 
v___x_509_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_507_);
v___x_510_ = lean_uint64_to_usize(v___x_509_);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_506_, v___x_510_, v___x_511_, v_x_507_, v_x_508_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_513_, lean_object* v_vals_514_, lean_object* v_i_515_, lean_object* v_k_516_){
_start:
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_array_get_size(v_keys_513_);
v___x_518_ = lean_nat_dec_lt(v_i_515_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_dec(v_i_515_);
v___x_519_ = lean_box(0);
return v___x_519_;
}
else
{
lean_object* v_k_x27_520_; uint8_t v___x_521_; 
v_k_x27_520_ = lean_array_fget_borrowed(v_keys_513_, v_i_515_);
v___x_521_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_516_, v_k_x27_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_i_515_, v___x_522_);
lean_dec(v_i_515_);
v_i_515_ = v___x_523_;
goto _start;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_array_fget_borrowed(v_vals_514_, v_i_515_);
lean_dec(v_i_515_);
lean_inc(v___x_525_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_527_, lean_object* v_vals_528_, lean_object* v_i_529_, lean_object* v_k_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_527_, v_vals_528_, v_i_529_, v_k_530_);
lean_dec_ref(v_k_530_);
lean_dec_ref(v_vals_528_);
lean_dec_ref(v_keys_527_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object* v_x_532_, size_t v_x_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_object* v_es_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_556_; 
v_es_535_ = lean_ctor_get(v_x_532_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_556_ == 0)
{
v___x_537_ = v_x_532_;
v_isShared_538_ = v_isSharedCheck_556_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_es_535_);
lean_dec(v_x_532_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_556_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; lean_object* v_j_543_; lean_object* v___x_544_; 
v___x_539_ = lean_box(2);
v___x_540_ = ((size_t)5ULL);
v___x_541_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1);
v___x_542_ = lean_usize_land(v_x_533_, v___x_541_);
v_j_543_ = lean_usize_to_nat(v___x_542_);
v___x_544_ = lean_array_get(v___x_539_, v_es_535_, v_j_543_);
lean_dec(v_j_543_);
lean_dec_ref(v_es_535_);
switch(lean_obj_tag(v___x_544_))
{
case 0:
{
lean_object* v_key_545_; lean_object* v_val_546_; uint8_t v___x_547_; 
v_key_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_key_545_);
v_val_546_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_val_546_);
lean_dec_ref(v___x_544_);
v___x_547_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_534_, v_key_545_);
lean_dec(v_key_545_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec(v_val_546_);
lean_del_object(v___x_537_);
v___x_548_ = lean_box(0);
return v___x_548_;
}
else
{
lean_object* v___x_550_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 1);
lean_ctor_set(v___x_537_, 0, v_val_546_);
v___x_550_ = v___x_537_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_val_546_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
case 1:
{
lean_object* v_node_552_; size_t v___x_553_; 
lean_del_object(v___x_537_);
v_node_552_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_node_552_);
lean_dec_ref(v___x_544_);
v___x_553_ = lean_usize_shift_right(v_x_533_, v___x_540_);
v_x_532_ = v_node_552_;
v_x_533_ = v___x_553_;
goto _start;
}
default: 
{
lean_object* v___x_555_; 
lean_del_object(v___x_537_);
v___x_555_ = lean_box(0);
return v___x_555_;
}
}
}
}
else
{
lean_object* v_ks_557_; lean_object* v_vs_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_ks_557_ = lean_ctor_get(v_x_532_, 0);
lean_inc_ref(v_ks_557_);
v_vs_558_ = lean_ctor_get(v_x_532_, 1);
lean_inc_ref(v_vs_558_);
lean_dec_ref(v_x_532_);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_ks_557_, v_vs_558_, v___x_559_, v_x_534_);
lean_dec_ref(v_vs_558_);
lean_dec_ref(v_ks_557_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
size_t v_x_57636__boxed_564_; lean_object* v_res_565_; 
v_x_57636__boxed_564_ = lean_unbox_usize(v_x_562_);
lean_dec(v_x_562_);
v_res_565_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_561_, v_x_57636__boxed_564_, v_x_563_);
lean_dec_ref(v_x_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint64_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_568_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_567_);
v___x_569_ = lean_uint64_to_usize(v___x_568_);
v___x_570_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_566_, v___x_569_, v_x_567_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_571_, v_x_572_);
lean_dec_ref(v_x_572_);
return v_res_573_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* lean_sym_simp(lean_object* v_e_u2081_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___y_590_; lean_object* v_a_591_; lean_object* v_e_u2082_607_; lean_object* v_h_u2081_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v_a_652_; lean_object* v_e_x27_653_; lean_object* v_proof_654_; uint8_t v_done_655_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v_fileName_705_; lean_object* v_fileMap_706_; lean_object* v_options_707_; lean_object* v_currRecDepth_708_; lean_object* v_maxRecDepth_709_; lean_object* v_ref_710_; lean_object* v_currNamespace_711_; lean_object* v_openDecls_712_; lean_object* v_initHeartbeats_713_; lean_object* v_maxHeartbeats_714_; lean_object* v_quotContext_715_; lean_object* v_currMacroScope_716_; uint8_t v_diag_717_; lean_object* v_cancelTk_x3f_718_; uint8_t v_suppressElabErrors_719_; lean_object* v_inheritedTraceOptions_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_894_; 
v_fileName_705_ = lean_ctor_get(v_a_586_, 0);
v_fileMap_706_ = lean_ctor_get(v_a_586_, 1);
v_options_707_ = lean_ctor_get(v_a_586_, 2);
v_currRecDepth_708_ = lean_ctor_get(v_a_586_, 3);
v_maxRecDepth_709_ = lean_ctor_get(v_a_586_, 4);
v_ref_710_ = lean_ctor_get(v_a_586_, 5);
v_currNamespace_711_ = lean_ctor_get(v_a_586_, 6);
v_openDecls_712_ = lean_ctor_get(v_a_586_, 7);
v_initHeartbeats_713_ = lean_ctor_get(v_a_586_, 8);
v_maxHeartbeats_714_ = lean_ctor_get(v_a_586_, 9);
v_quotContext_715_ = lean_ctor_get(v_a_586_, 10);
v_currMacroScope_716_ = lean_ctor_get(v_a_586_, 11);
v_diag_717_ = lean_ctor_get_uint8(v_a_586_, sizeof(void*)*14);
v_cancelTk_x3f_718_ = lean_ctor_get(v_a_586_, 12);
v_suppressElabErrors_719_ = lean_ctor_get_uint8(v_a_586_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_720_ = lean_ctor_get(v_a_586_, 13);
v_isSharedCheck_894_ = !lean_is_exclusive(v_a_586_);
if (v_isSharedCheck_894_ == 0)
{
v___x_722_ = v_a_586_;
v_isShared_723_ = v_isSharedCheck_894_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_inheritedTraceOptions_720_);
lean_inc(v_cancelTk_x3f_718_);
lean_inc(v_currMacroScope_716_);
lean_inc(v_quotContext_715_);
lean_inc(v_maxHeartbeats_714_);
lean_inc(v_initHeartbeats_713_);
lean_inc(v_openDecls_712_);
lean_inc(v_currNamespace_711_);
lean_inc(v_ref_710_);
lean_inc(v_maxRecDepth_709_);
lean_inc(v_currRecDepth_708_);
lean_inc(v_options_707_);
lean_inc(v_fileMap_706_);
lean_inc(v_fileName_705_);
lean_dec(v_a_586_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_894_;
goto v_resetjp_721_;
}
v___jp_589_:
{
lean_object* v___x_592_; lean_object* v_numSteps_593_; lean_object* v_cache_594_; lean_object* v_funext_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_605_; 
v___x_592_ = lean_st_ref_take(v___y_590_);
v_numSteps_593_ = lean_ctor_get(v___x_592_, 0);
v_cache_594_ = lean_ctor_get(v___x_592_, 1);
v_funext_595_ = lean_ctor_get(v___x_592_, 2);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_605_ == 0)
{
v___x_597_ = v___x_592_;
v_isShared_598_ = v_isSharedCheck_605_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_funext_595_);
lean_inc(v_cache_594_);
lean_inc(v_numSteps_593_);
lean_dec(v___x_592_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_605_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_601_; 
lean_inc_ref(v_a_591_);
v___x_599_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_cache_594_, v_e_u2081_578_, v_a_591_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 1, v___x_599_);
v___x_601_ = v___x_597_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_numSteps_593_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_funext_595_);
v___x_601_ = v_reuseFailAlloc_604_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_st_ref_set(v___y_590_, v___x_601_);
lean_dec(v___y_590_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v_a_591_);
return v___x_603_;
}
}
}
v___jp_606_:
{
lean_object* v___x_618_; 
lean_inc(v___y_617_);
lean_inc_ref(v___y_616_);
lean_inc(v___y_615_);
lean_inc_ref(v___y_614_);
lean_inc(v___y_613_);
lean_inc(v___y_611_);
lean_inc_ref(v_e_u2082_607_);
v___x_618_ = lean_sym_simp(v_e_u2082_607_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v___x_618_);
if (lean_obj_tag(v_a_619_) == 0)
{
uint8_t v_done_620_; lean_object* v___x_621_; 
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
v_done_620_ = lean_ctor_get_uint8(v_a_619_, 0);
lean_dec_ref(v_a_619_);
v___x_621_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_621_, 0, v_e_u2082_607_);
lean_ctor_set(v___x_621_, 1, v_h_u2081_608_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*2, v_done_620_);
v___y_590_ = v___y_611_;
v_a_591_ = v___x_621_;
goto v___jp_589_;
}
else
{
lean_object* v_e_x27_622_; lean_object* v_proof_623_; uint8_t v_done_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_641_; 
v_e_x27_622_ = lean_ctor_get(v_a_619_, 0);
v_proof_623_ = lean_ctor_get(v_a_619_, 1);
v_done_624_ = lean_ctor_get_uint8(v_a_619_, sizeof(void*)*2);
v_isSharedCheck_641_ = !lean_is_exclusive(v_a_619_);
if (v_isSharedCheck_641_ == 0)
{
v___x_626_ = v_a_619_;
v_isShared_627_ = v_isSharedCheck_641_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_proof_623_);
lean_inc(v_e_x27_622_);
lean_dec(v_a_619_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_641_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; 
lean_inc_ref(v_e_x27_622_);
lean_inc_ref(v_e_u2081_578_);
v___x_628_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_578_, v_e_u2082_607_, v_h_u2081_608_, v_e_x27_622_, v_proof_623_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_613_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref(v___x_628_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v_a_629_);
v___x_631_ = v___x_626_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_e_x27_622_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_a_629_);
lean_ctor_set_uint8(v_reuseFailAlloc_632_, sizeof(void*)*2, v_done_624_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
v___y_590_ = v___y_611_;
v_a_591_ = v___x_631_;
goto v___jp_589_;
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_del_object(v___x_626_);
lean_dec_ref(v_e_x27_622_);
lean_dec(v___y_611_);
lean_dec_ref(v_e_u2081_578_);
v_a_633_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_628_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_628_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
}
else
{
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec(v___y_611_);
lean_dec_ref(v_h_u2081_608_);
lean_dec_ref(v_e_u2082_607_);
lean_dec_ref(v_e_u2081_578_);
return v___x_618_;
}
}
v___jp_642_:
{
if (v_done_655_ == 0)
{
lean_dec_ref(v_a_652_);
v_e_u2082_607_ = v_e_x27_653_;
v_h_u2081_608_ = v_proof_654_;
v___y_609_ = v___y_650_;
v___y_610_ = v___y_645_;
v___y_611_ = v___y_648_;
v___y_612_ = v___y_644_;
v___y_613_ = v___y_646_;
v___y_614_ = v___y_647_;
v___y_615_ = v___y_643_;
v___y_616_ = v___y_651_;
v___y_617_ = v___y_649_;
goto v___jp_606_;
}
else
{
lean_object* v___x_656_; lean_object* v_numSteps_657_; lean_object* v_cache_658_; lean_object* v_funext_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_proof_654_);
lean_dec_ref(v_e_x27_653_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
v___x_656_ = lean_st_ref_take(v___y_648_);
v_numSteps_657_ = lean_ctor_get(v___x_656_, 0);
v_cache_658_ = lean_ctor_get(v___x_656_, 1);
v_funext_659_ = lean_ctor_get(v___x_656_, 2);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_669_ == 0)
{
v___x_661_ = v___x_656_;
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_funext_659_);
lean_inc(v_cache_658_);
lean_inc(v_numSteps_657_);
lean_dec(v___x_656_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
lean_inc_ref(v_a_652_);
v___x_663_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_cache_658_, v_e_u2081_578_, v_a_652_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_numSteps_657_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_funext_659_);
v___x_665_ = v_reuseFailAlloc_668_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_st_ref_set(v___y_648_, v___x_665_);
lean_dec(v___y_648_);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v_a_652_);
return v___x_667_;
}
}
}
}
v___jp_670_:
{
if (lean_obj_tag(v___y_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_704_; 
v_a_681_ = lean_ctor_get(v___y_680_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___y_680_);
if (v_isSharedCheck_704_ == 0)
{
v___x_683_ = v___y_680_;
v_isShared_684_ = v_isSharedCheck_704_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___y_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_704_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
if (lean_obj_tag(v_a_681_) == 0)
{
lean_object* v___x_685_; lean_object* v_numSteps_686_; lean_object* v_cache_687_; lean_object* v_funext_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
v___x_685_ = lean_st_ref_take(v___y_676_);
v_numSteps_686_ = lean_ctor_get(v___x_685_, 0);
v_cache_687_ = lean_ctor_get(v___x_685_, 1);
v_funext_688_ = lean_ctor_get(v___x_685_, 2);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_700_ == 0)
{
v___x_690_ = v___x_685_;
v_isShared_691_ = v_isSharedCheck_700_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_funext_688_);
lean_inc(v_cache_687_);
lean_inc(v_numSteps_686_);
lean_dec(v___x_685_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_700_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
lean_inc_ref(v_a_681_);
v___x_692_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_cache_687_, v_e_u2081_578_, v_a_681_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_numSteps_686_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_funext_688_);
v___x_694_ = v_reuseFailAlloc_699_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_st_ref_set(v___y_676_, v___x_694_);
lean_dec(v___y_676_);
if (v_isShared_684_ == 0)
{
v___x_697_ = v___x_683_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_681_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v_e_x27_701_; lean_object* v_proof_702_; uint8_t v_done_703_; 
lean_del_object(v___x_683_);
v_e_x27_701_ = lean_ctor_get(v_a_681_, 0);
lean_inc_ref(v_e_x27_701_);
v_proof_702_ = lean_ctor_get(v_a_681_, 1);
lean_inc_ref(v_proof_702_);
v_done_703_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*2);
v___y_643_ = v___y_671_;
v___y_644_ = v___y_672_;
v___y_645_ = v___y_673_;
v___y_646_ = v___y_674_;
v___y_647_ = v___y_675_;
v___y_648_ = v___y_676_;
v___y_649_ = v___y_678_;
v___y_650_ = v___y_677_;
v___y_651_ = v___y_679_;
v_a_652_ = v_a_681_;
v_e_x27_653_ = v_e_x27_701_;
v_proof_654_ = v_proof_702_;
v_done_655_ = v_done_703_;
goto v___jp_642_;
}
}
}
else
{
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v_e_u2081_578_);
return v___y_680_;
}
}
v_resetjp_721_:
{
uint8_t v___x_724_; 
v___x_724_ = lean_nat_dec_eq(v_currRecDepth_708_, v_maxRecDepth_709_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_st_ref_get(v_a_581_);
v___x_726_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_580_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_884_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_884_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_884_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_884_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v_numSteps_731_; lean_object* v_maxSteps_732_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v_numSteps_731_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_numSteps_731_);
lean_dec(v___x_725_);
v_maxSteps_732_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_maxSteps_732_);
lean_dec(v_a_727_);
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_add(v_currRecDepth_708_, v___x_837_);
lean_dec(v_currRecDepth_708_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 3, v___x_838_);
v___x_840_ = v___x_722_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_fileName_705_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_fileMap_706_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_options_707_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_883_, 4, v_maxRecDepth_709_);
lean_ctor_set(v_reuseFailAlloc_883_, 5, v_ref_710_);
lean_ctor_set(v_reuseFailAlloc_883_, 6, v_currNamespace_711_);
lean_ctor_set(v_reuseFailAlloc_883_, 7, v_openDecls_712_);
lean_ctor_set(v_reuseFailAlloc_883_, 8, v_initHeartbeats_713_);
lean_ctor_set(v_reuseFailAlloc_883_, 9, v_maxHeartbeats_714_);
lean_ctor_set(v_reuseFailAlloc_883_, 10, v_quotContext_715_);
lean_ctor_set(v_reuseFailAlloc_883_, 11, v_currMacroScope_716_);
lean_ctor_set(v_reuseFailAlloc_883_, 12, v_cancelTk_x3f_718_);
lean_ctor_set(v_reuseFailAlloc_883_, 13, v_inheritedTraceOptions_720_);
lean_ctor_set_uint8(v_reuseFailAlloc_883_, sizeof(void*)*14, v_diag_717_);
lean_ctor_set_uint8(v_reuseFailAlloc_883_, sizeof(void*)*14 + 1, v_suppressElabErrors_719_);
v___x_840_ = v_reuseFailAlloc_883_;
goto v_reusejp_839_;
}
v___jp_733_:
{
lean_object* v___x_744_; lean_object* v_cache_745_; lean_object* v_funext_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_835_; 
v___x_744_ = lean_st_ref_take(v___y_737_);
v_cache_745_ = lean_ctor_get(v___x_744_, 1);
v_funext_746_ = lean_ctor_get(v___x_744_, 2);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v___x_744_, 0);
lean_dec(v_unused_836_);
v___x_748_ = v___x_744_;
v_isShared_749_ = v_isSharedCheck_835_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_funext_746_);
lean_inc(v_cache_745_);
lean_dec(v___x_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_835_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___y_734_);
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___y_734_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_cache_745_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_funext_746_);
v___x_751_ = v_reuseFailAlloc_834_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v_pre_753_; lean_object* v___x_754_; 
v___x_752_ = lean_st_ref_set(v___y_737_, v___x_751_);
v_pre_753_ = lean_ctor_get(v___y_735_, 0);
lean_inc_ref(v_pre_753_);
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v_e_u2081_578_);
v___x_754_ = lean_apply_11(v_pre_753_, v_e_u2081_578_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, lean_box(0));
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_833_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_833_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_833_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_833_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
if (lean_obj_tag(v_a_755_) == 0)
{
uint8_t v_done_759_; 
v_done_759_ = lean_ctor_get_uint8(v_a_755_, 0);
if (v_done_759_ == 0)
{
lean_object* v___x_760_; 
lean_dec_ref(v_a_755_);
lean_del_object(v___x_757_);
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v_e_u2081_578_);
v___x_760_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(v_e_u2081_578_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
v___x_762_ = lean_box(0);
if (lean_obj_tag(v_a_761_) == 0)
{
uint8_t v_done_763_; 
v_done_763_ = lean_ctor_get_uint8(v_a_761_, 0);
lean_dec_ref(v_a_761_);
if (v_done_763_ == 0)
{
lean_object* v___x_764_; 
lean_dec_ref(v___x_760_);
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v_e_u2081_578_);
v___x_764_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_762_, v_e_u2081_578_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
v___y_671_ = v___y_741_;
v___y_672_ = v___y_738_;
v___y_673_ = v___y_736_;
v___y_674_ = v___y_739_;
v___y_675_ = v___y_740_;
v___y_676_ = v___y_737_;
v___y_677_ = v___y_735_;
v___y_678_ = v___y_743_;
v___y_679_ = v___y_742_;
v___y_680_ = v___x_764_;
goto v___jp_670_;
}
else
{
v___y_671_ = v___y_741_;
v___y_672_ = v___y_738_;
v___y_673_ = v___y_736_;
v___y_674_ = v___y_739_;
v___y_675_ = v___y_740_;
v___y_676_ = v___y_737_;
v___y_677_ = v___y_735_;
v___y_678_ = v___y_743_;
v___y_679_ = v___y_742_;
v___y_680_ = v___x_760_;
goto v___jp_670_;
}
}
else
{
uint8_t v_done_765_; 
v_done_765_ = lean_ctor_get_uint8(v_a_761_, sizeof(void*)*2);
if (v_done_765_ == 0)
{
lean_object* v_e_x27_766_; lean_object* v_proof_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v___x_760_);
v_e_x27_766_ = lean_ctor_get(v_a_761_, 0);
v_proof_767_ = lean_ctor_get(v_a_761_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_a_761_);
if (v_isSharedCheck_797_ == 0)
{
v___x_769_ = v_a_761_;
v_isShared_770_ = v_isSharedCheck_797_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_proof_767_);
lean_inc(v_e_x27_766_);
lean_dec(v_a_761_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_797_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; 
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v_e_x27_766_);
v___x_771_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_762_, v_e_x27_766_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref(v___x_771_);
if (lean_obj_tag(v_a_772_) == 0)
{
uint8_t v_done_773_; lean_object* v___x_775_; 
v_done_773_ = lean_ctor_get_uint8(v_a_772_, 0);
lean_dec_ref(v_a_772_);
lean_inc_ref(v_proof_767_);
lean_inc_ref(v_e_x27_766_);
if (v_isShared_770_ == 0)
{
v___x_775_ = v___x_769_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_e_x27_766_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_proof_767_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*2, v_done_773_);
v___y_643_ = v___y_741_;
v___y_644_ = v___y_738_;
v___y_645_ = v___y_736_;
v___y_646_ = v___y_739_;
v___y_647_ = v___y_740_;
v___y_648_ = v___y_737_;
v___y_649_ = v___y_743_;
v___y_650_ = v___y_735_;
v___y_651_ = v___y_742_;
v_a_652_ = v___x_775_;
v_e_x27_653_ = v_e_x27_766_;
v_proof_654_ = v_proof_767_;
v_done_655_ = v_done_773_;
goto v___jp_642_;
}
}
else
{
lean_object* v_e_x27_777_; lean_object* v_proof_778_; uint8_t v_done_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_796_; 
lean_del_object(v___x_769_);
v_e_x27_777_ = lean_ctor_get(v_a_772_, 0);
v_proof_778_ = lean_ctor_get(v_a_772_, 1);
v_done_779_ = lean_ctor_get_uint8(v_a_772_, sizeof(void*)*2);
v_isSharedCheck_796_ = !lean_is_exclusive(v_a_772_);
if (v_isSharedCheck_796_ == 0)
{
v___x_781_ = v_a_772_;
v_isShared_782_ = v_isSharedCheck_796_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_proof_778_);
lean_inc(v_e_x27_777_);
lean_dec(v_a_772_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_796_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; 
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc_ref(v_e_x27_777_);
lean_inc_ref(v_e_u2081_578_);
v___x_783_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_578_, v_e_x27_766_, v_proof_767_, v_e_x27_777_, v_proof_778_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
lean_inc(v_a_784_);
lean_inc_ref(v_e_x27_777_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_a_784_);
v___x_786_ = v___x_781_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_e_x27_777_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_a_784_);
lean_ctor_set_uint8(v_reuseFailAlloc_787_, sizeof(void*)*2, v_done_779_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v___y_643_ = v___y_741_;
v___y_644_ = v___y_738_;
v___y_645_ = v___y_736_;
v___y_646_ = v___y_739_;
v___y_647_ = v___y_740_;
v___y_648_ = v___y_737_;
v___y_649_ = v___y_743_;
v___y_650_ = v___y_735_;
v___y_651_ = v___y_742_;
v_a_652_ = v___x_786_;
v_e_x27_653_ = v_e_x27_777_;
v_proof_654_ = v_a_784_;
v_done_655_ = v_done_779_;
goto v___jp_642_;
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_del_object(v___x_781_);
lean_dec_ref(v_e_x27_777_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v_e_u2081_578_);
v_a_788_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_783_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_783_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_769_);
lean_dec_ref(v_proof_767_);
lean_dec_ref(v_e_x27_766_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v_e_u2081_578_);
return v___x_771_;
}
}
}
else
{
lean_dec_ref(v_a_761_);
v___y_671_ = v___y_741_;
v___y_672_ = v___y_738_;
v___y_673_ = v___y_736_;
v___y_674_ = v___y_739_;
v___y_675_ = v___y_740_;
v___y_676_ = v___y_737_;
v___y_677_ = v___y_735_;
v___y_678_ = v___y_743_;
v___y_679_ = v___y_742_;
v___y_680_ = v___x_760_;
goto v___jp_670_;
}
}
}
else
{
v___y_671_ = v___y_741_;
v___y_672_ = v___y_738_;
v___y_673_ = v___y_736_;
v___y_674_ = v___y_739_;
v___y_675_ = v___y_740_;
v___y_676_ = v___y_737_;
v___y_677_ = v___y_735_;
v___y_678_ = v___y_743_;
v___y_679_ = v___y_742_;
v___y_680_ = v___x_760_;
goto v___jp_670_;
}
}
else
{
lean_object* v___x_798_; lean_object* v_numSteps_799_; lean_object* v_cache_800_; lean_object* v_funext_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_813_; 
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
v___x_798_ = lean_st_ref_take(v___y_737_);
v_numSteps_799_ = lean_ctor_get(v___x_798_, 0);
v_cache_800_ = lean_ctor_get(v___x_798_, 1);
v_funext_801_ = lean_ctor_get(v___x_798_, 2);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_813_ == 0)
{
v___x_803_ = v___x_798_;
v_isShared_804_ = v_isSharedCheck_813_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_funext_801_);
lean_inc(v_cache_800_);
lean_inc(v_numSteps_799_);
lean_dec(v___x_798_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_813_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
lean_inc_ref(v_a_755_);
v___x_805_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_cache_800_, v_e_u2081_578_, v_a_755_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_805_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_numSteps_799_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_funext_801_);
v___x_807_ = v_reuseFailAlloc_812_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_st_ref_set(v___y_737_, v___x_807_);
lean_dec(v___y_737_);
if (v_isShared_758_ == 0)
{
v___x_810_ = v___x_757_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_755_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
else
{
uint8_t v_done_814_; 
v_done_814_ = lean_ctor_get_uint8(v_a_755_, sizeof(void*)*2);
if (v_done_814_ == 0)
{
lean_object* v_e_x27_815_; lean_object* v_proof_816_; 
lean_del_object(v___x_757_);
v_e_x27_815_ = lean_ctor_get(v_a_755_, 0);
lean_inc_ref(v_e_x27_815_);
v_proof_816_ = lean_ctor_get(v_a_755_, 1);
lean_inc_ref(v_proof_816_);
lean_dec_ref(v_a_755_);
v_e_u2082_607_ = v_e_x27_815_;
v_h_u2081_608_ = v_proof_816_;
v___y_609_ = v___y_735_;
v___y_610_ = v___y_736_;
v___y_611_ = v___y_737_;
v___y_612_ = v___y_738_;
v___y_613_ = v___y_739_;
v___y_614_ = v___y_740_;
v___y_615_ = v___y_741_;
v___y_616_ = v___y_742_;
v___y_617_ = v___y_743_;
goto v___jp_606_;
}
else
{
lean_object* v___x_817_; lean_object* v_numSteps_818_; lean_object* v_cache_819_; lean_object* v_funext_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_832_; 
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
v___x_817_ = lean_st_ref_take(v___y_737_);
v_numSteps_818_ = lean_ctor_get(v___x_817_, 0);
v_cache_819_ = lean_ctor_get(v___x_817_, 1);
v_funext_820_ = lean_ctor_get(v___x_817_, 2);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_832_ == 0)
{
v___x_822_ = v___x_817_;
v_isShared_823_ = v_isSharedCheck_832_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_funext_820_);
lean_inc(v_cache_819_);
lean_inc(v_numSteps_818_);
lean_dec(v___x_817_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_832_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
lean_inc_ref(v_a_755_);
v___x_824_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_cache_819_, v_e_u2081_578_, v_a_755_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_numSteps_818_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_funext_820_);
v___x_826_ = v_reuseFailAlloc_831_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_st_ref_set(v___y_737_, v___x_826_);
lean_dec(v___y_737_);
if (v_isShared_758_ == 0)
{
v___x_829_ = v___x_757_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_755_);
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
}
}
}
else
{
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v_e_u2081_578_);
return v___x_754_;
}
}
}
}
v_reusejp_839_:
{
lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; uint8_t v___x_872_; 
v___x_872_ = lean_nat_dec_le(v_maxSteps_732_, v_numSteps_731_);
lean_dec(v_maxSteps_732_);
if (v___x_872_ == 0)
{
v___y_842_ = v_a_579_;
v___y_843_ = v_a_580_;
v___y_844_ = v_a_581_;
v___y_845_ = v_a_582_;
v___y_846_ = v_a_583_;
v___y_847_ = v_a_584_;
v___y_848_ = v_a_585_;
v___y_849_ = v_a_587_;
goto v___jp_841_;
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_numSteps_731_);
lean_del_object(v___x_729_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_e_u2081_578_);
v___x_873_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2, &l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
v___x_874_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_873_, v_a_584_, v_a_585_, v___x_840_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v___x_840_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
v___jp_841_:
{
lean_object* v___x_850_; lean_object* v_cache_851_; lean_object* v___x_852_; 
v___x_850_ = lean_st_ref_get(v___y_844_);
v_cache_851_ = lean_ctor_get(v___x_850_, 1);
lean_inc_ref(v_cache_851_);
lean_dec(v___x_850_);
v___x_852_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_cache_851_, v_e_u2081_578_);
if (lean_obj_tag(v___x_852_) == 1)
{
lean_object* v_val_853_; lean_object* v___x_855_; 
lean_dec(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___x_840_);
lean_dec(v_numSteps_731_);
lean_dec_ref(v_e_u2081_578_);
v_val_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_val_853_);
lean_dec_ref(v___x_852_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v_val_853_);
v___x_855_ = v___x_729_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_val_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
lean_dec(v___x_852_);
lean_del_object(v___x_729_);
v___x_857_ = lean_nat_add(v_numSteps_731_, v___x_837_);
lean_dec(v_numSteps_731_);
v___x_858_ = lean_unsigned_to_nat(1000u);
v___x_859_ = lean_nat_mod(v___x_857_, v___x_858_);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_nat_dec_eq(v___x_859_, v___x_860_);
lean_dec(v___x_859_);
if (v___x_861_ == 0)
{
v___y_734_ = v___x_857_;
v___y_735_ = v___y_842_;
v___y_736_ = v___y_843_;
v___y_737_ = v___y_844_;
v___y_738_ = v___y_845_;
v___y_739_ = v___y_846_;
v___y_740_ = v___y_847_;
v___y_741_ = v___y_848_;
v___y_742_ = v___x_840_;
v___y_743_ = v___y_849_;
goto v___jp_733_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0));
v___x_863_ = l_Lean_Core_checkSystem(v___x_862_, v___x_840_, v___y_849_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_dec_ref(v___x_863_);
v___y_734_ = v___x_857_;
v___y_735_ = v___y_842_;
v___y_736_ = v___y_843_;
v___y_737_ = v___y_844_;
v___y_738_ = v___y_845_;
v___y_739_ = v___y_846_;
v___y_740_ = v___y_847_;
v___y_741_ = v___y_848_;
v___y_742_ = v___x_840_;
v___y_743_ = v___y_849_;
goto v___jp_733_;
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v___x_857_);
lean_dec(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___x_840_);
lean_dec_ref(v_e_u2081_578_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v___x_725_);
lean_del_object(v___x_722_);
lean_dec_ref(v_inheritedTraceOptions_720_);
lean_dec(v_cancelTk_x3f_718_);
lean_dec(v_currMacroScope_716_);
lean_dec(v_quotContext_715_);
lean_dec(v_maxHeartbeats_714_);
lean_dec(v_initHeartbeats_713_);
lean_dec(v_openDecls_712_);
lean_dec(v_currNamespace_711_);
lean_dec(v_ref_710_);
lean_dec(v_maxRecDepth_709_);
lean_dec(v_currRecDepth_708_);
lean_dec_ref(v_options_707_);
lean_dec_ref(v_fileMap_706_);
lean_dec_ref(v_fileName_705_);
lean_dec(v_a_587_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_e_u2081_578_);
v_a_885_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_726_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_726_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
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
lean_object* v___x_893_; 
lean_del_object(v___x_722_);
lean_dec_ref(v_inheritedTraceOptions_720_);
lean_dec(v_cancelTk_x3f_718_);
lean_dec(v_currMacroScope_716_);
lean_dec(v_quotContext_715_);
lean_dec(v_maxHeartbeats_714_);
lean_dec(v_initHeartbeats_713_);
lean_dec(v_openDecls_712_);
lean_dec(v_currNamespace_711_);
lean_dec(v_maxRecDepth_709_);
lean_dec(v_currRecDepth_708_);
lean_dec_ref(v_options_707_);
lean_dec_ref(v_fileMap_706_);
lean_dec_ref(v_fileName_705_);
lean_dec(v_a_587_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_e_u2081_578_);
v___x_893_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_ref_710_);
return v___x_893_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object* v_e_u2081_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = lean_sym_simp(v_e_u2081_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object* v_00_u03b2_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_x_908_, v_x_909_, v_x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object* v_00_u03b2_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_913_, v_x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object* v_00_u03b2_916_, lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(v_00_u03b2_916_, v_x_917_, v_x_918_);
lean_dec_ref(v_x_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object* v_00_u03b2_920_, lean_object* v_x_921_, size_t v_x_922_, size_t v_x_923_, lean_object* v_x_924_, lean_object* v_x_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_921_, v_x_922_, v_x_923_, v_x_924_, v_x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
size_t v_x_58309__boxed_933_; size_t v_x_58310__boxed_934_; lean_object* v_res_935_; 
v_x_58309__boxed_933_ = lean_unbox_usize(v_x_929_);
lean_dec(v_x_929_);
v_x_58310__boxed_934_ = lean_unbox_usize(v_x_930_);
lean_dec(v_x_930_);
v_res_935_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(v_00_u03b2_927_, v_x_928_, v_x_58309__boxed_933_, v_x_58310__boxed_934_, v_x_931_, v_x_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object* v_00_u03b2_936_, lean_object* v_x_937_, size_t v_x_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_937_, v_x_938_, v_x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_941_, lean_object* v_x_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
size_t v_x_58326__boxed_945_; lean_object* v_res_946_; 
v_x_58326__boxed_945_ = lean_unbox_usize(v_x_943_);
lean_dec(v_x_943_);
v_res_946_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(v_00_u03b2_941_, v_x_942_, v_x_58326__boxed_945_, v_x_944_);
lean_dec_ref(v_x_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_947_, lean_object* v_n_948_, lean_object* v_k_949_, lean_object* v_v_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v_n_948_, v_k_949_, v_v_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_952_, size_t v_depth_953_, lean_object* v_keys_954_, lean_object* v_vals_955_, lean_object* v_heq_956_, lean_object* v_i_957_, lean_object* v_entries_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_953_, v_keys_954_, v_vals_955_, v_i_957_, v_entries_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_960_, lean_object* v_depth_961_, lean_object* v_keys_962_, lean_object* v_vals_963_, lean_object* v_heq_964_, lean_object* v_i_965_, lean_object* v_entries_966_){
_start:
{
size_t v_depth_boxed_967_; lean_object* v_res_968_; 
v_depth_boxed_967_ = lean_unbox_usize(v_depth_961_);
lean_dec(v_depth_961_);
v_res_968_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(v_00_u03b2_960_, v_depth_boxed_967_, v_keys_962_, v_vals_963_, v_heq_964_, v_i_965_, v_entries_966_);
lean_dec_ref(v_vals_963_);
lean_dec_ref(v_keys_962_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_969_, lean_object* v_keys_970_, lean_object* v_vals_971_, lean_object* v_heq_972_, lean_object* v_i_973_, lean_object* v_k_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_970_, v_vals_971_, v_i_973_, v_k_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_976_, lean_object* v_keys_977_, lean_object* v_vals_978_, lean_object* v_heq_979_, lean_object* v_i_980_, lean_object* v_k_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(v_00_u03b2_976_, v_keys_977_, v_vals_978_, v_heq_979_, v_i_980_, v_k_981_);
lean_dec_ref(v_k_981_);
lean_dec_ref(v_vals_978_);
lean_dec_ref(v_keys_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_x_984_, v_x_985_, v_x_986_, v_x_987_);
return v___x_988_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Main(builtin);
}
#ifdef __cplusplus
}
#endif
