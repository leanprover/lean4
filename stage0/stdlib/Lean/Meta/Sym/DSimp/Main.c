// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Main
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.DSimp.DSimproc import Lean.Meta.Sym.DSimp.App import Lean.Meta.Sym.DSimp.Lambda import Lean.Meta.Sym.DSimp.Forall import Lean.Meta.Sym.DSimp.Let import Lean.Meta.Sym.AlphaShareBuilder
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
lean_object* l_Lean_stringToMessageData(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "unexpected kernel projection term during simplification"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "\npre-process and fold them as projection applications"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "`dsimp` failed: maximum number of steps exceeded"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2;
LEAN_EXPORT lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(lean_object* v_d_1_, lean_object* v_e_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v_debug_15_; 
v___x_14_ = lean_st_ref_get(v___y_4_);
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*11);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_dec_ref_known(v___x_16_, 1);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
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
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg___boxed(lean_object* v_d_25_, lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_25_, v_e_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(lean_object* v_d_35_, lean_object* v_e_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_35_, v_e_36_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___boxed(lean_object* v_d_48_, lean_object* v_e_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(v_d_48_, v_e_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec(v___y_51_);
lean_dec(v___y_50_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(lean_object* v_msgData_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1___boxed(lean_object* v_msgData_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msgData_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(lean_object* v_msg_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_ref_89_; lean_object* v___x_90_; lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_99_; 
v_ref_89_ = lean_ctor_get(v___y_86_, 5);
v___x_90_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msg_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg___boxed(lean_object* v_msg_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1));
v___x_111_ = l_Lean_stringToMessageData(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3));
v___x_114_ = l_Lean_stringToMessageData(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(lean_object* v_e_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_a_127_; 
switch(lean_obj_tag(v_e_115_))
{
case 5:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Meta_Sym_DSimp_dsimpAppArgs(v_e_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
return v___x_131_;
}
case 6:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Meta_Sym_DSimp_dsimpLambda(v_e_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
return v___x_132_;
}
case 7:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Sym_DSimp_dsimpForall(v_e_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
return v___x_133_;
}
case 8:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Sym_DSimp_dsimpLet(v_e_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
return v___x_134_;
}
case 10:
{
lean_object* v_data_135_; lean_object* v_expr_136_; lean_object* v___x_137_; 
v_data_135_ = lean_ctor_get(v_e_115_, 0);
v_expr_136_ = lean_ctor_get(v_e_115_, 1);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v_a_118_);
lean_inc(v_a_117_);
lean_inc(v_a_116_);
lean_inc_ref(v_expr_136_);
v___x_137_ = lean_sym_dsimp(v_expr_136_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_160_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_160_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_160_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_160_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
if (lean_obj_tag(v_a_138_) == 0)
{
lean_object* v___x_142_; lean_object* v___x_144_; 
lean_dec_ref_known(v_a_138_, 0);
lean_dec_ref_known(v_e_115_, 2);
v___x_142_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0));
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
else
{
lean_object* v_e_x27_146_; size_t v___x_147_; size_t v___x_148_; uint8_t v___x_149_; 
lean_del_object(v___x_140_);
v_e_x27_146_ = lean_ctor_get(v_a_138_, 0);
lean_inc_ref(v_e_x27_146_);
lean_dec_ref_known(v_a_138_, 1);
v___x_147_ = lean_ptr_addr(v_expr_136_);
v___x_148_ = lean_ptr_addr(v_e_x27_146_);
v___x_149_ = lean_usize_dec_eq(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
lean_inc(v_data_135_);
lean_dec_ref_known(v_e_115_, 2);
v___x_150_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_data_135_, v_e_x27_146_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v___x_150_, 1);
v_a_127_ = v_a_151_;
goto v___jp_126_;
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_150_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_150_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_146_);
v_a_127_ = v_e_115_;
goto v___jp_126_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_115_, 2);
return v___x_137_;
}
}
case 11:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2);
v___x_162_ = l_Lean_indentExpr(v_e_115_);
v___x_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4);
v___x_165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_165_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
return v___x_166_;
}
default: 
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref(v_e_115_);
v___x_167_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0));
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
v___jp_126_:
{
uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = 0;
v___x_129_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_129_, 0, v_a_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*1, v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___boxed(lean_object* v_e_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec(v_a_171_);
lean_dec(v_a_170_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(lean_object* v_00_u03b1_181_, lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_182_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___boxed(lean_object* v_00_u03b1_194_, lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(v_00_u03b1_194_, v_msg_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec(v___y_197_);
lean_dec(v___y_196_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(lean_object* v_e_209_, lean_object* v_r_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_213_; lean_object* v_numSteps_214_; lean_object* v_cache_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_227_; 
v___x_213_ = lean_st_ref_take(v_a_211_);
v_numSteps_214_ = lean_ctor_get(v___x_213_, 0);
v_cache_215_ = lean_ctor_get(v___x_213_, 1);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_227_ == 0)
{
v___x_217_ = v___x_213_;
v_isShared_218_ = v_isSharedCheck_227_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_cache_215_);
lean_inc(v_numSteps_214_);
lean_dec(v___x_213_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_227_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___f_219_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0));
v___f_220_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1));
lean_inc_ref(v_r_210_);
v___x_221_ = l_Lean_PersistentHashMap_insert___redArg(v___f_219_, v___f_220_, v_cache_215_, v_e_209_, v_r_210_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_221_);
v___x_223_ = v___x_217_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_numSteps_214_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_221_);
v___x_223_ = v_reuseFailAlloc_226_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_st_ref_set(v_a_211_, v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v_r_210_);
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___boxed(lean_object* v_e_228_, lean_object* v_r_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(v_e_228_, v_r_229_, v_a_230_);
lean_dec(v_a_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(lean_object* v_e_233_, lean_object* v_r_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; lean_object* v_numSteps_246_; lean_object* v_cache_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_259_; 
v___x_245_ = lean_st_ref_take(v_a_237_);
v_numSteps_246_ = lean_ctor_get(v___x_245_, 0);
v_cache_247_ = lean_ctor_get(v___x_245_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_259_ == 0)
{
v___x_249_ = v___x_245_;
v_isShared_250_ = v_isSharedCheck_259_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_cache_247_);
lean_inc(v_numSteps_246_);
lean_dec(v___x_245_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_259_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___f_251_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0));
v___f_252_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1));
lean_inc_ref(v_r_234_);
v___x_253_ = l_Lean_PersistentHashMap_insert___redArg(v___f_251_, v___f_252_, v_cache_247_, v_e_233_, v_r_234_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v___x_253_);
v___x_255_ = v___x_249_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_numSteps_246_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v___x_253_);
v___x_255_ = v_reuseFailAlloc_258_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_st_ref_set(v_a_237_, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v_r_234_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___boxed(lean_object* v_e_260_, lean_object* v_r_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(v_e_260_, v_r_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec(v_a_263_);
lean_dec(v_a_262_);
return v_res_272_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = l_Lean_maxRecDepthErrorMessage;
v___x_279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3);
v___x_281_ = l_Lean_MessageData_ofFormat(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4);
v___x_283_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2));
v___x_284_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(lean_object* v_ref_285_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v_ref_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___boxed(lean_object* v_ref_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(lean_object* v_00_u03b1_293_, lean_object* v_ref_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_294_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___boxed(lean_object* v_00_u03b1_306_, lean_object* v_ref_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(v_00_u03b1_306_, v_ref_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec(v___y_309_);
lean_dec(v___y_308_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(lean_object* v_x_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_post_331_; lean_object* v___x_332_; 
v_post_331_ = lean_ctor_get(v___y_321_, 1);
lean_inc_ref(v_post_331_);
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v___y_323_);
lean_inc(v___y_322_);
lean_inc(v___y_321_);
v___x_332_ = lean_apply_11(v_post_331_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, lean_box(0));
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0___boxed(lean_object* v_x_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v_x_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec(v___y_336_);
lean_dec(v___y_335_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_ks_350_; lean_object* v_vs_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_377_; 
v_ks_350_ = lean_ctor_get(v_x_346_, 0);
v_vs_351_ = lean_ctor_get(v_x_346_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_x_346_);
if (v_isSharedCheck_377_ == 0)
{
v___x_353_ = v_x_346_;
v_isShared_354_ = v_isSharedCheck_377_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_vs_351_);
lean_inc(v_ks_350_);
lean_dec(v_x_346_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_377_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_array_get_size(v_ks_350_);
v___x_356_ = lean_nat_dec_lt(v_x_347_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
lean_dec(v_x_347_);
v___x_357_ = lean_array_push(v_ks_350_, v_x_348_);
v___x_358_ = lean_array_push(v_vs_351_, v_x_349_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_358_);
lean_ctor_set(v___x_353_, 0, v___x_357_);
v___x_360_ = v___x_353_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
else
{
lean_object* v_k_x27_362_; size_t v___x_363_; size_t v___x_364_; uint8_t v___x_365_; 
v_k_x27_362_ = lean_array_fget_borrowed(v_ks_350_, v_x_347_);
v___x_363_ = lean_ptr_addr(v_x_348_);
v___x_364_ = lean_ptr_addr(v_k_x27_362_);
v___x_365_ = lean_usize_dec_eq(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_367_; 
if (v_isShared_354_ == 0)
{
v___x_367_ = v___x_353_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_ks_350_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_vs_351_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_nat_add(v_x_347_, v___x_368_);
lean_dec(v_x_347_);
v_x_346_ = v___x_367_;
v_x_347_ = v___x_369_;
goto _start;
}
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_372_ = lean_array_fset(v_ks_350_, v_x_347_, v_x_348_);
v___x_373_ = lean_array_fset(v_vs_351_, v_x_347_, v_x_349_);
lean_dec(v_x_347_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_373_);
lean_ctor_set(v___x_353_, 0, v___x_372_);
v___x_375_ = v___x_353_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_n_378_, lean_object* v_k_379_, lean_object* v_v_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_n_378_, v___x_381_, v_k_379_, v_v_380_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(lean_object* v_x_384_, size_t v_x_385_, size_t v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v_es_389_; size_t v___x_390_; size_t v___x_391_; lean_object* v_j_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_es_389_ = lean_ctor_get(v_x_384_, 0);
v___x_390_ = ((size_t)31ULL);
v___x_391_ = lean_usize_land(v_x_385_, v___x_390_);
v_j_392_ = lean_usize_to_nat(v___x_391_);
v___x_393_ = lean_array_get_size(v_es_389_);
v___x_394_ = lean_nat_dec_lt(v_j_392_, v___x_393_);
if (v___x_394_ == 0)
{
lean_dec(v_j_392_);
lean_dec(v_x_388_);
lean_dec_ref(v_x_387_);
return v_x_384_;
}
else
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_435_; 
lean_inc_ref(v_es_389_);
v_isSharedCheck_435_ = !lean_is_exclusive(v_x_384_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v_x_384_, 0);
lean_dec(v_unused_436_);
v___x_396_ = v_x_384_;
v_isShared_397_ = v_isSharedCheck_435_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_x_384_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_435_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_v_398_; lean_object* v___x_399_; lean_object* v_xs_x27_400_; lean_object* v___y_402_; 
v_v_398_ = lean_array_fget(v_es_389_, v_j_392_);
v___x_399_ = lean_box(0);
v_xs_x27_400_ = lean_array_fset(v_es_389_, v_j_392_, v___x_399_);
switch(lean_obj_tag(v_v_398_))
{
case 0:
{
lean_object* v_key_407_; lean_object* v_val_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_420_; 
v_key_407_ = lean_ctor_get(v_v_398_, 0);
v_val_408_ = lean_ctor_get(v_v_398_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_v_398_);
if (v_isSharedCheck_420_ == 0)
{
v___x_410_ = v_v_398_;
v_isShared_411_ = v_isSharedCheck_420_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_val_408_);
lean_inc(v_key_407_);
lean_dec(v_v_398_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_420_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
size_t v___x_412_; size_t v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_ptr_addr(v_x_387_);
v___x_413_ = lean_ptr_addr(v_key_407_);
v___x_414_ = lean_usize_dec_eq(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_del_object(v___x_410_);
v___x_415_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_407_, v_val_408_, v_x_387_, v_x_388_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
v___y_402_ = v___x_416_;
goto v___jp_401_;
}
else
{
lean_object* v___x_418_; 
lean_dec(v_val_408_);
lean_dec(v_key_407_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v_x_388_);
lean_ctor_set(v___x_410_, 0, v_x_387_);
v___x_418_ = v___x_410_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_x_387_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_x_388_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
v___y_402_ = v___x_418_;
goto v___jp_401_;
}
}
}
}
case 1:
{
lean_object* v_node_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_433_; 
v_node_421_ = lean_ctor_get(v_v_398_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_v_398_);
if (v_isSharedCheck_433_ == 0)
{
v___x_423_ = v_v_398_;
v_isShared_424_ = v_isSharedCheck_433_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_node_421_);
lean_dec(v_v_398_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_433_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
size_t v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_425_ = ((size_t)5ULL);
v___x_426_ = lean_usize_shift_right(v_x_385_, v___x_425_);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_x_386_, v___x_427_);
v___x_429_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_node_421_, v___x_426_, v___x_428_, v_x_387_, v_x_388_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_429_);
v___x_431_ = v___x_423_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v___y_402_ = v___x_431_;
goto v___jp_401_;
}
}
}
default: 
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v_x_387_);
lean_ctor_set(v___x_434_, 1, v_x_388_);
v___y_402_ = v___x_434_;
goto v___jp_401_;
}
}
v___jp_401_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_array_fset(v_xs_x27_400_, v_j_392_, v___y_402_);
lean_dec(v_j_392_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_403_);
v___x_405_ = v___x_396_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
else
{
lean_object* v_ks_437_; lean_object* v_vs_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_458_; 
v_ks_437_ = lean_ctor_get(v_x_384_, 0);
v_vs_438_ = lean_ctor_get(v_x_384_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_384_);
if (v_isSharedCheck_458_ == 0)
{
v___x_440_ = v_x_384_;
v_isShared_441_ = v_isSharedCheck_458_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_vs_438_);
lean_inc(v_ks_437_);
lean_dec(v_x_384_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_458_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_ks_437_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_vs_438_);
v___x_443_ = v_reuseFailAlloc_457_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v_newNode_444_; uint8_t v___y_446_; size_t v___x_452_; uint8_t v___x_453_; 
v_newNode_444_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v___x_443_, v_x_387_, v_x_388_);
v___x_452_ = ((size_t)7ULL);
v___x_453_ = lean_usize_dec_le(v___x_452_, v_x_386_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_444_);
v___x_455_ = lean_unsigned_to_nat(4u);
v___x_456_ = lean_nat_dec_lt(v___x_454_, v___x_455_);
lean_dec(v___x_454_);
v___y_446_ = v___x_456_;
goto v___jp_445_;
}
else
{
v___y_446_ = v___x_453_;
goto v___jp_445_;
}
v___jp_445_:
{
if (v___y_446_ == 0)
{
lean_object* v_ks_447_; lean_object* v_vs_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_ks_447_ = lean_ctor_get(v_newNode_444_, 0);
lean_inc_ref(v_ks_447_);
v_vs_448_ = lean_ctor_get(v_newNode_444_, 1);
lean_inc_ref(v_vs_448_);
lean_dec_ref(v_newNode_444_);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0);
v___x_451_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_x_386_, v_ks_447_, v_vs_448_, v___x_449_, v___x_450_);
lean_dec_ref(v_vs_448_);
lean_dec_ref(v_ks_447_);
return v___x_451_;
}
else
{
return v_newNode_444_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_459_, lean_object* v_keys_460_, lean_object* v_vals_461_, lean_object* v_i_462_, lean_object* v_entries_463_){
_start:
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_array_get_size(v_keys_460_);
v___x_465_ = lean_nat_dec_lt(v_i_462_, v___x_464_);
if (v___x_465_ == 0)
{
lean_dec(v_i_462_);
return v_entries_463_;
}
else
{
lean_object* v_k_466_; lean_object* v_v_467_; size_t v___x_468_; size_t v___x_469_; size_t v___x_470_; uint64_t v___x_471_; size_t v_h_472_; size_t v___x_473_; lean_object* v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v_h_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_k_466_ = lean_array_fget_borrowed(v_keys_460_, v_i_462_);
v_v_467_ = lean_array_fget_borrowed(v_vals_461_, v_i_462_);
v___x_468_ = lean_ptr_addr(v_k_466_);
v___x_469_ = ((size_t)3ULL);
v___x_470_ = lean_usize_shift_right(v___x_468_, v___x_469_);
v___x_471_ = lean_usize_to_uint64(v___x_470_);
v_h_472_ = lean_uint64_to_usize(v___x_471_);
v___x_473_ = ((size_t)5ULL);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_sub(v_depth_459_, v___x_475_);
v___x_477_ = lean_usize_mul(v___x_473_, v___x_476_);
v_h_478_ = lean_usize_shift_right(v_h_472_, v___x_477_);
v___x_479_ = lean_nat_add(v_i_462_, v___x_474_);
lean_dec(v_i_462_);
lean_inc(v_v_467_);
lean_inc(v_k_466_);
v___x_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_entries_463_, v_h_478_, v_depth_459_, v_k_466_, v_v_467_);
v_i_462_ = v___x_479_;
v_entries_463_ = v___x_480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_482_, lean_object* v_keys_483_, lean_object* v_vals_484_, lean_object* v_i_485_, lean_object* v_entries_486_){
_start:
{
size_t v_depth_boxed_487_; lean_object* v_res_488_; 
v_depth_boxed_487_ = lean_unbox_usize(v_depth_482_);
lean_dec(v_depth_482_);
v_res_488_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_487_, v_keys_483_, v_vals_484_, v_i_485_, v_entries_486_);
lean_dec_ref(v_vals_484_);
lean_dec_ref(v_keys_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
size_t v_x_42504__boxed_494_; size_t v_x_42505__boxed_495_; lean_object* v_res_496_; 
v_x_42504__boxed_494_ = lean_unbox_usize(v_x_490_);
lean_dec(v_x_490_);
v_x_42505__boxed_495_ = lean_unbox_usize(v_x_491_);
lean_dec(v_x_491_);
v_res_496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_489_, v_x_42504__boxed_494_, v_x_42505__boxed_495_, v_x_492_, v_x_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; uint64_t v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v___x_500_ = lean_ptr_addr(v_x_498_);
v___x_501_ = ((size_t)3ULL);
v___x_502_ = lean_usize_shift_right(v___x_500_, v___x_501_);
v___x_503_ = lean_usize_to_uint64(v___x_502_);
v___x_504_ = lean_uint64_to_usize(v___x_503_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_497_, v___x_504_, v___x_505_, v_x_498_, v_x_499_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_507_, lean_object* v_vals_508_, lean_object* v_i_509_, lean_object* v_k_510_){
_start:
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_array_get_size(v_keys_507_);
v___x_512_ = lean_nat_dec_lt(v_i_509_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_i_509_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
else
{
lean_object* v_k_x27_514_; size_t v___x_515_; size_t v___x_516_; uint8_t v___x_517_; 
v_k_x27_514_ = lean_array_fget_borrowed(v_keys_507_, v_i_509_);
v___x_515_ = lean_ptr_addr(v_k_510_);
v___x_516_ = lean_ptr_addr(v_k_x27_514_);
v___x_517_ = lean_usize_dec_eq(v___x_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_i_509_, v___x_518_);
lean_dec(v_i_509_);
v_i_509_ = v___x_519_;
goto _start;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_array_fget_borrowed(v_vals_508_, v_i_509_);
lean_dec(v_i_509_);
lean_inc(v___x_521_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_523_, lean_object* v_vals_524_, lean_object* v_i_525_, lean_object* v_k_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_523_, v_vals_524_, v_i_525_, v_k_526_);
lean_dec_ref(v_k_526_);
lean_dec_ref(v_vals_524_);
lean_dec_ref(v_keys_523_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(lean_object* v_x_528_, size_t v_x_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_es_531_; lean_object* v___x_532_; size_t v___x_533_; size_t v___x_534_; lean_object* v_j_535_; lean_object* v___x_536_; 
v_es_531_ = lean_ctor_get(v_x_528_, 0);
v___x_532_ = lean_box(2);
v___x_533_ = ((size_t)31ULL);
v___x_534_ = lean_usize_land(v_x_529_, v___x_533_);
v_j_535_ = lean_usize_to_nat(v___x_534_);
v___x_536_ = lean_array_get_borrowed(v___x_532_, v_es_531_, v_j_535_);
lean_dec(v_j_535_);
switch(lean_obj_tag(v___x_536_))
{
case 0:
{
lean_object* v_key_537_; lean_object* v_val_538_; size_t v___x_539_; size_t v___x_540_; uint8_t v___x_541_; 
v_key_537_ = lean_ctor_get(v___x_536_, 0);
v_val_538_ = lean_ctor_get(v___x_536_, 1);
v___x_539_ = lean_ptr_addr(v_x_530_);
v___x_540_ = lean_ptr_addr(v_key_537_);
v___x_541_ = lean_usize_dec_eq(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = lean_box(0);
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
lean_inc(v_val_538_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_val_538_);
return v___x_543_;
}
}
case 1:
{
lean_object* v_node_544_; size_t v___x_545_; size_t v___x_546_; 
v_node_544_ = lean_ctor_get(v___x_536_, 0);
v___x_545_ = ((size_t)5ULL);
v___x_546_ = lean_usize_shift_right(v_x_529_, v___x_545_);
v_x_528_ = v_node_544_;
v_x_529_ = v___x_546_;
goto _start;
}
default: 
{
lean_object* v___x_548_; 
v___x_548_ = lean_box(0);
return v___x_548_;
}
}
}
else
{
lean_object* v_ks_549_; lean_object* v_vs_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_ks_549_ = lean_ctor_get(v_x_528_, 0);
v_vs_550_ = lean_ctor_get(v_x_528_, 1);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_ks_549_, v_vs_550_, v___x_551_, v_x_530_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
size_t v_x_42709__boxed_556_; lean_object* v_res_557_; 
v_x_42709__boxed_556_ = lean_unbox_usize(v_x_554_);
lean_dec(v_x_554_);
v_res_557_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_553_, v_x_42709__boxed_556_, v_x_555_);
lean_dec_ref(v_x_555_);
lean_dec_ref(v_x_553_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; uint64_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_560_ = lean_ptr_addr(v_x_559_);
v___x_561_ = ((size_t)3ULL);
v___x_562_ = lean_usize_shift_right(v___x_560_, v___x_561_);
v___x_563_ = lean_usize_to_uint64(v___x_562_);
v___x_564_ = lean_uint64_to_usize(v___x_563_);
v___x_565_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_558_, v___x_564_, v_x_559_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg___boxed(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_566_, v_x_567_);
lean_dec_ref(v_x_567_);
lean_dec_ref(v_x_566_);
return v_res_568_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* lean_sym_dsimp(lean_object* v_e_u2081_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_r_585_; lean_object* v___y_586_; lean_object* v_e_u2082_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v_a_625_; lean_object* v_e_x27_626_; uint8_t v_done_627_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v_fileName_642_; lean_object* v_fileMap_643_; lean_object* v_options_644_; lean_object* v_currRecDepth_645_; lean_object* v_maxRecDepth_646_; lean_object* v_ref_647_; lean_object* v_currNamespace_648_; lean_object* v_openDecls_649_; lean_object* v_initHeartbeats_650_; lean_object* v_maxHeartbeats_651_; lean_object* v_quotContext_652_; lean_object* v_currMacroScope_653_; uint8_t v_diag_654_; lean_object* v_cancelTk_x3f_655_; uint8_t v_suppressElabErrors_656_; lean_object* v_inheritedTraceOptions_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_769_; 
v_fileName_642_ = lean_ctor_get(v_a_581_, 0);
v_fileMap_643_ = lean_ctor_get(v_a_581_, 1);
v_options_644_ = lean_ctor_get(v_a_581_, 2);
v_currRecDepth_645_ = lean_ctor_get(v_a_581_, 3);
v_maxRecDepth_646_ = lean_ctor_get(v_a_581_, 4);
v_ref_647_ = lean_ctor_get(v_a_581_, 5);
v_currNamespace_648_ = lean_ctor_get(v_a_581_, 6);
v_openDecls_649_ = lean_ctor_get(v_a_581_, 7);
v_initHeartbeats_650_ = lean_ctor_get(v_a_581_, 8);
v_maxHeartbeats_651_ = lean_ctor_get(v_a_581_, 9);
v_quotContext_652_ = lean_ctor_get(v_a_581_, 10);
v_currMacroScope_653_ = lean_ctor_get(v_a_581_, 11);
v_diag_654_ = lean_ctor_get_uint8(v_a_581_, sizeof(void*)*14);
v_cancelTk_x3f_655_ = lean_ctor_get(v_a_581_, 12);
v_suppressElabErrors_656_ = lean_ctor_get_uint8(v_a_581_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_657_ = lean_ctor_get(v_a_581_, 13);
v_isSharedCheck_769_ = !lean_is_exclusive(v_a_581_);
if (v_isSharedCheck_769_ == 0)
{
v___x_659_ = v_a_581_;
v_isShared_660_ = v_isSharedCheck_769_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_inheritedTraceOptions_657_);
lean_inc(v_cancelTk_x3f_655_);
lean_inc(v_currMacroScope_653_);
lean_inc(v_quotContext_652_);
lean_inc(v_maxHeartbeats_651_);
lean_inc(v_initHeartbeats_650_);
lean_inc(v_openDecls_649_);
lean_inc(v_currNamespace_648_);
lean_inc(v_ref_647_);
lean_inc(v_maxRecDepth_646_);
lean_inc(v_currRecDepth_645_);
lean_inc(v_options_644_);
lean_inc(v_fileMap_643_);
lean_inc(v_fileName_642_);
lean_dec(v_a_581_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_769_;
goto v_resetjp_658_;
}
v___jp_584_:
{
lean_object* v___x_587_; lean_object* v_numSteps_588_; lean_object* v_cache_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_599_; 
v___x_587_ = lean_st_ref_take(v___y_586_);
v_numSteps_588_ = lean_ctor_get(v___x_587_, 0);
v_cache_589_ = lean_ctor_get(v___x_587_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_599_ == 0)
{
v___x_591_ = v___x_587_;
v_isShared_592_ = v_isSharedCheck_599_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_cache_589_);
lean_inc(v_numSteps_588_);
lean_dec(v___x_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_599_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
lean_inc_ref(v_r_585_);
v___x_593_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_cache_589_, v_e_u2081_573_, v_r_585_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_numSteps_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_593_);
v___x_595_ = v_reuseFailAlloc_598_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_st_ref_set(v___y_586_, v___x_595_);
lean_dec(v___y_586_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v_r_585_);
return v___x_597_;
}
}
}
v___jp_600_:
{
lean_object* v___x_611_; 
lean_inc(v___y_604_);
lean_inc_ref(v_e_u2082_601_);
v___x_611_ = lean_sym_dsimp(v_e_u2082_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_611_, 1);
if (lean_obj_tag(v_a_612_) == 0)
{
uint8_t v_done_613_; lean_object* v___x_614_; 
v_done_613_ = lean_ctor_get_uint8(v_a_612_, 0);
lean_dec_ref_known(v_a_612_, 0);
v___x_614_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_614_, 0, v_e_u2082_601_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*1, v_done_613_);
v_r_585_ = v___x_614_;
v___y_586_ = v___y_604_;
goto v___jp_584_;
}
else
{
lean_dec_ref(v_e_u2082_601_);
v_r_585_ = v_a_612_;
v___y_586_ = v___y_604_;
goto v___jp_584_;
}
}
else
{
lean_dec(v___y_604_);
lean_dec_ref(v_e_u2082_601_);
lean_dec_ref(v_e_u2081_573_);
return v___x_611_;
}
}
v___jp_615_:
{
if (v_done_627_ == 0)
{
lean_dec_ref(v_a_625_);
v_e_u2082_601_ = v_e_x27_626_;
v___y_602_ = v___y_622_;
v___y_603_ = v___y_621_;
v___y_604_ = v___y_620_;
v___y_605_ = v___y_618_;
v___y_606_ = v___y_624_;
v___y_607_ = v___y_619_;
v___y_608_ = v___y_623_;
v___y_609_ = v___y_617_;
v___y_610_ = v___y_616_;
goto v___jp_600_;
}
else
{
lean_dec_ref(v_e_x27_626_);
lean_dec(v___y_624_);
lean_dec(v___y_623_);
lean_dec(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
v_r_585_ = v_a_625_;
v___y_586_ = v___y_620_;
goto v___jp_584_;
}
}
v___jp_628_:
{
if (lean_obj_tag(v___y_638_) == 0)
{
lean_object* v_a_639_; 
v_a_639_ = lean_ctor_get(v___y_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___y_638_, 1);
if (lean_obj_tag(v_a_639_) == 0)
{
lean_dec(v___y_637_);
lean_dec(v___y_636_);
lean_dec(v___y_635_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v___y_629_);
v_r_585_ = v_a_639_;
v___y_586_ = v___y_634_;
goto v___jp_584_;
}
else
{
lean_object* v_e_x27_640_; uint8_t v_done_641_; 
v_e_x27_640_ = lean_ctor_get(v_a_639_, 0);
lean_inc_ref(v_e_x27_640_);
v_done_641_ = lean_ctor_get_uint8(v_a_639_, sizeof(void*)*1);
v___y_616_ = v___y_631_;
v___y_617_ = v___y_630_;
v___y_618_ = v___y_629_;
v___y_619_ = v___y_632_;
v___y_620_ = v___y_634_;
v___y_621_ = v___y_633_;
v___y_622_ = v___y_635_;
v___y_623_ = v___y_636_;
v___y_624_ = v___y_637_;
v_a_625_ = v_a_639_;
v_e_x27_626_ = v_e_x27_640_;
v_done_627_ = v_done_641_;
goto v___jp_615_;
}
}
else
{
lean_dec(v___y_637_);
lean_dec(v___y_636_);
lean_dec(v___y_635_);
lean_dec(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec_ref(v_e_u2081_573_);
return v___y_638_;
}
}
v_resetjp_658_:
{
lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_nat_dec_eq(v_maxRecDepth_646_, v___x_765_);
if (v___x_766_ == 0)
{
uint8_t v___x_767_; 
v___x_767_ = lean_nat_dec_eq(v_currRecDepth_645_, v_maxRecDepth_646_);
if (v___x_767_ == 0)
{
goto v___jp_746_;
}
else
{
lean_object* v___x_768_; 
lean_del_object(v___x_659_);
lean_dec_ref(v_inheritedTraceOptions_657_);
lean_dec(v_cancelTk_x3f_655_);
lean_dec(v_currMacroScope_653_);
lean_dec(v_quotContext_652_);
lean_dec(v_maxHeartbeats_651_);
lean_dec(v_initHeartbeats_650_);
lean_dec(v_openDecls_649_);
lean_dec(v_currNamespace_648_);
lean_dec(v_maxRecDepth_646_);
lean_dec(v_currRecDepth_645_);
lean_dec_ref(v_options_644_);
lean_dec_ref(v_fileMap_643_);
lean_dec_ref(v_fileName_642_);
lean_dec(v_a_582_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_e_u2081_573_);
v___x_768_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_647_);
return v___x_768_;
}
}
else
{
goto v___jp_746_;
}
v___jp_661_:
{
lean_object* v___x_672_; lean_object* v_cache_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_706_; 
v___x_672_ = lean_st_ref_take(v___y_665_);
v_cache_673_ = lean_ctor_get(v___x_672_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v___x_672_, 0);
lean_dec(v_unused_707_);
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_706_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_cache_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_706_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___y_662_);
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___y_662_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_cache_673_);
v___x_678_ = v_reuseFailAlloc_705_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v_pre_680_; lean_object* v___x_681_; 
v___x_679_ = lean_st_ref_set(v___y_665_, v___x_678_);
v_pre_680_ = lean_ctor_get(v___y_663_, 0);
lean_inc_ref(v_pre_680_);
lean_inc(v___y_671_);
lean_inc_ref(v___y_670_);
lean_inc(v___y_669_);
lean_inc_ref(v___y_668_);
lean_inc(v___y_667_);
lean_inc_ref(v___y_666_);
lean_inc(v___y_665_);
lean_inc(v___y_664_);
lean_inc(v___y_663_);
lean_inc_ref(v_e_u2081_573_);
v___x_681_ = lean_apply_11(v_pre_680_, v_e_u2081_573_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, lean_box(0));
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
if (lean_obj_tag(v_a_682_) == 0)
{
uint8_t v_done_683_; 
v_done_683_ = lean_ctor_get_uint8(v_a_682_, 0);
if (v_done_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec_ref_known(v_a_682_, 0);
lean_inc_ref(v_e_u2081_573_);
v___x_684_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_u2081_573_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
v___x_686_ = lean_box(0);
if (lean_obj_tag(v_a_685_) == 0)
{
uint8_t v_done_687_; 
v_done_687_ = lean_ctor_get_uint8(v_a_685_, 0);
lean_dec_ref_known(v_a_685_, 0);
if (v_done_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec_ref_known(v___x_684_, 1);
lean_inc_ref(v_e_u2081_573_);
v___x_688_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v___x_686_, v_e_u2081_573_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
v___y_629_ = v___y_666_;
v___y_630_ = v___y_670_;
v___y_631_ = v___y_671_;
v___y_632_ = v___y_668_;
v___y_633_ = v___y_664_;
v___y_634_ = v___y_665_;
v___y_635_ = v___y_663_;
v___y_636_ = v___y_669_;
v___y_637_ = v___y_667_;
v___y_638_ = v___x_688_;
goto v___jp_628_;
}
else
{
v___y_629_ = v___y_666_;
v___y_630_ = v___y_670_;
v___y_631_ = v___y_671_;
v___y_632_ = v___y_668_;
v___y_633_ = v___y_664_;
v___y_634_ = v___y_665_;
v___y_635_ = v___y_663_;
v___y_636_ = v___y_669_;
v___y_637_ = v___y_667_;
v___y_638_ = v___x_684_;
goto v___jp_628_;
}
}
else
{
uint8_t v_done_689_; 
v_done_689_ = lean_ctor_get_uint8(v_a_685_, sizeof(void*)*1);
if (v_done_689_ == 0)
{
lean_object* v_e_x27_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref_known(v___x_684_, 1);
v_e_x27_690_ = lean_ctor_get(v_a_685_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_a_685_);
if (v_isSharedCheck_702_ == 0)
{
v___x_692_ = v_a_685_;
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_e_x27_690_);
lean_dec(v_a_685_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; 
lean_inc_ref(v_e_x27_690_);
v___x_694_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v___x_686_, v_e_x27_690_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
if (lean_obj_tag(v_a_695_) == 0)
{
uint8_t v_done_696_; lean_object* v___x_698_; 
v_done_696_ = lean_ctor_get_uint8(v_a_695_, 0);
lean_dec_ref_known(v_a_695_, 0);
lean_inc_ref(v_e_x27_690_);
if (v_isShared_693_ == 0)
{
v___x_698_ = v___x_692_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_e_x27_690_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*1, v_done_696_);
v___y_616_ = v___y_671_;
v___y_617_ = v___y_670_;
v___y_618_ = v___y_666_;
v___y_619_ = v___y_668_;
v___y_620_ = v___y_665_;
v___y_621_ = v___y_664_;
v___y_622_ = v___y_663_;
v___y_623_ = v___y_669_;
v___y_624_ = v___y_667_;
v_a_625_ = v___x_698_;
v_e_x27_626_ = v_e_x27_690_;
v_done_627_ = v_done_696_;
goto v___jp_615_;
}
}
else
{
lean_object* v_e_x27_700_; uint8_t v_done_701_; 
lean_del_object(v___x_692_);
lean_dec_ref(v_e_x27_690_);
v_e_x27_700_ = lean_ctor_get(v_a_695_, 0);
lean_inc_ref(v_e_x27_700_);
v_done_701_ = lean_ctor_get_uint8(v_a_695_, sizeof(void*)*1);
v___y_616_ = v___y_671_;
v___y_617_ = v___y_670_;
v___y_618_ = v___y_666_;
v___y_619_ = v___y_668_;
v___y_620_ = v___y_665_;
v___y_621_ = v___y_664_;
v___y_622_ = v___y_663_;
v___y_623_ = v___y_669_;
v___y_624_ = v___y_667_;
v_a_625_ = v_a_695_;
v_e_x27_626_ = v_e_x27_700_;
v_done_627_ = v_done_701_;
goto v___jp_615_;
}
}
else
{
lean_del_object(v___x_692_);
lean_dec_ref(v_e_x27_690_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v_e_u2081_573_);
return v___x_694_;
}
}
}
else
{
lean_dec_ref_known(v_a_685_, 1);
v___y_629_ = v___y_666_;
v___y_630_ = v___y_670_;
v___y_631_ = v___y_671_;
v___y_632_ = v___y_668_;
v___y_633_ = v___y_664_;
v___y_634_ = v___y_665_;
v___y_635_ = v___y_663_;
v___y_636_ = v___y_669_;
v___y_637_ = v___y_667_;
v___y_638_ = v___x_684_;
goto v___jp_628_;
}
}
}
else
{
v___y_629_ = v___y_666_;
v___y_630_ = v___y_670_;
v___y_631_ = v___y_671_;
v___y_632_ = v___y_668_;
v___y_633_ = v___y_664_;
v___y_634_ = v___y_665_;
v___y_635_ = v___y_663_;
v___y_636_ = v___y_669_;
v___y_637_ = v___y_667_;
v___y_638_ = v___x_684_;
goto v___jp_628_;
}
}
else
{
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_664_);
lean_dec(v___y_663_);
v_r_585_ = v_a_682_;
v___y_586_ = v___y_665_;
goto v___jp_584_;
}
}
else
{
uint8_t v_done_703_; 
v_done_703_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*1);
if (v_done_703_ == 0)
{
lean_object* v_e_x27_704_; 
v_e_x27_704_ = lean_ctor_get(v_a_682_, 0);
lean_inc_ref(v_e_x27_704_);
lean_dec_ref_known(v_a_682_, 1);
v_e_u2082_601_ = v_e_x27_704_;
v___y_602_ = v___y_663_;
v___y_603_ = v___y_664_;
v___y_604_ = v___y_665_;
v___y_605_ = v___y_666_;
v___y_606_ = v___y_667_;
v___y_607_ = v___y_668_;
v___y_608_ = v___y_669_;
v___y_609_ = v___y_670_;
v___y_610_ = v___y_671_;
goto v___jp_600_;
}
else
{
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_664_);
lean_dec(v___y_663_);
v_r_585_ = v_a_682_;
v___y_586_ = v___y_665_;
goto v___jp_584_;
}
}
}
else
{
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v_e_u2081_573_);
return v___x_681_;
}
}
}
}
v___jp_708_:
{
lean_object* v___x_720_; lean_object* v_cache_721_; lean_object* v___x_722_; 
v___x_720_ = lean_st_ref_get(v___y_713_);
v_cache_721_ = lean_ctor_get(v___x_720_, 1);
lean_inc_ref(v_cache_721_);
lean_dec(v___x_720_);
v___x_722_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_cache_721_, v_e_u2081_573_);
lean_dec_ref(v_cache_721_);
if (lean_obj_tag(v___x_722_) == 1)
{
lean_object* v_val_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec(v___y_712_);
lean_dec(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v_e_u2081_573_);
v_val_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_val_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set_tag(v___x_725_, 0);
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_val_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
lean_dec(v___x_722_);
v___x_731_ = lean_nat_add(v___y_710_, v___y_709_);
lean_dec(v___y_710_);
v___x_732_ = lean_unsigned_to_nat(1000u);
v___x_733_ = lean_nat_mod(v___x_731_, v___x_732_);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_nat_dec_eq(v___x_733_, v___x_734_);
lean_dec(v___x_733_);
if (v___x_735_ == 0)
{
v___y_662_ = v___x_731_;
v___y_663_ = v___y_711_;
v___y_664_ = v___y_712_;
v___y_665_ = v___y_713_;
v___y_666_ = v___y_714_;
v___y_667_ = v___y_715_;
v___y_668_ = v___y_716_;
v___y_669_ = v___y_717_;
v___y_670_ = v___y_718_;
v___y_671_ = v___y_719_;
goto v___jp_661_;
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0));
v___x_737_ = l_Lean_Core_checkSystem(v___x_736_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_dec_ref_known(v___x_737_, 1);
v___y_662_ = v___x_731_;
v___y_663_ = v___y_711_;
v___y_664_ = v___y_712_;
v___y_665_ = v___y_713_;
v___y_666_ = v___y_714_;
v___y_667_ = v___y_715_;
v___y_668_ = v___y_716_;
v___y_669_ = v___y_717_;
v___y_670_ = v___y_718_;
v___y_671_ = v___y_719_;
goto v___jp_661_;
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v___x_731_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v_e_u2081_573_);
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
v___jp_746_:
{
lean_object* v___x_747_; lean_object* v_numSteps_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_747_ = lean_st_ref_get(v_a_576_);
v_numSteps_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_numSteps_748_);
lean_dec(v___x_747_);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v_currRecDepth_645_, v___x_749_);
lean_dec(v_currRecDepth_645_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 3, v___x_750_);
v___x_752_ = v___x_659_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_fileName_642_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_fileMap_643_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_options_644_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_maxRecDepth_646_);
lean_ctor_set(v_reuseFailAlloc_764_, 5, v_ref_647_);
lean_ctor_set(v_reuseFailAlloc_764_, 6, v_currNamespace_648_);
lean_ctor_set(v_reuseFailAlloc_764_, 7, v_openDecls_649_);
lean_ctor_set(v_reuseFailAlloc_764_, 8, v_initHeartbeats_650_);
lean_ctor_set(v_reuseFailAlloc_764_, 9, v_maxHeartbeats_651_);
lean_ctor_set(v_reuseFailAlloc_764_, 10, v_quotContext_652_);
lean_ctor_set(v_reuseFailAlloc_764_, 11, v_currMacroScope_653_);
lean_ctor_set(v_reuseFailAlloc_764_, 12, v_cancelTk_x3f_655_);
lean_ctor_set(v_reuseFailAlloc_764_, 13, v_inheritedTraceOptions_657_);
lean_ctor_set_uint8(v_reuseFailAlloc_764_, sizeof(void*)*14, v_diag_654_);
lean_ctor_set_uint8(v_reuseFailAlloc_764_, sizeof(void*)*14 + 1, v_suppressElabErrors_656_);
v___x_752_ = v_reuseFailAlloc_764_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
uint8_t v___x_753_; 
v___x_753_ = lean_nat_dec_le(v_a_575_, v_numSteps_748_);
if (v___x_753_ == 0)
{
v___y_709_ = v___x_749_;
v___y_710_ = v_numSteps_748_;
v___y_711_ = v_a_574_;
v___y_712_ = v_a_575_;
v___y_713_ = v_a_576_;
v___y_714_ = v_a_577_;
v___y_715_ = v_a_578_;
v___y_716_ = v_a_579_;
v___y_717_ = v_a_580_;
v___y_718_ = v___x_752_;
v___y_719_ = v_a_582_;
goto v___jp_708_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_numSteps_748_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_e_u2081_573_);
v___x_754_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2);
v___x_755_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_754_, v_a_579_, v_a_580_, v___x_752_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v___x_752_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___boxed(lean_object* v_e_u2081_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = lean_sym_dsimp(v_e_u2081_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0(lean_object* v_00_u03b2_782_, lean_object* v_x_783_, lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_x_783_, v_x_784_, v_x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(lean_object* v_00_u03b2_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_788_, v_x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___boxed(lean_object* v_00_u03b2_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(v_00_u03b2_791_, v_x_792_, v_x_793_);
lean_dec_ref(v_x_793_);
lean_dec_ref(v_x_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, size_t v_x_797_, size_t v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_796_, v_x_797_, v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
size_t v_x_43143__boxed_808_; size_t v_x_43144__boxed_809_; lean_object* v_res_810_; 
v_x_43143__boxed_808_ = lean_unbox_usize(v_x_804_);
lean_dec(v_x_804_);
v_x_43144__boxed_809_ = lean_unbox_usize(v_x_805_);
lean_dec(v_x_805_);
v_res_810_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(v_00_u03b2_802_, v_x_803_, v_x_43143__boxed_808_, v_x_43144__boxed_809_, v_x_806_, v_x_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(lean_object* v_00_u03b2_811_, lean_object* v_x_812_, size_t v_x_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_812_, v_x_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
size_t v_x_43160__boxed_820_; lean_object* v_res_821_; 
v_x_43160__boxed_820_ = lean_unbox_usize(v_x_818_);
lean_dec(v_x_818_);
v_res_821_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(v_00_u03b2_816_, v_x_817_, v_x_43160__boxed_820_, v_x_819_);
lean_dec_ref(v_x_819_);
lean_dec_ref(v_x_817_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_822_, lean_object* v_n_823_, lean_object* v_k_824_, lean_object* v_v_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v_n_823_, v_k_824_, v_v_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_827_, size_t v_depth_828_, lean_object* v_keys_829_, lean_object* v_vals_830_, lean_object* v_heq_831_, lean_object* v_i_832_, lean_object* v_entries_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_828_, v_keys_829_, v_vals_830_, v_i_832_, v_entries_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_835_, lean_object* v_depth_836_, lean_object* v_keys_837_, lean_object* v_vals_838_, lean_object* v_heq_839_, lean_object* v_i_840_, lean_object* v_entries_841_){
_start:
{
size_t v_depth_boxed_842_; lean_object* v_res_843_; 
v_depth_boxed_842_ = lean_unbox_usize(v_depth_836_);
lean_dec(v_depth_836_);
v_res_843_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(v_00_u03b2_835_, v_depth_boxed_842_, v_keys_837_, v_vals_838_, v_heq_839_, v_i_840_, v_entries_841_);
lean_dec_ref(v_vals_838_);
lean_dec_ref(v_keys_837_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_844_, lean_object* v_keys_845_, lean_object* v_vals_846_, lean_object* v_heq_847_, lean_object* v_i_848_, lean_object* v_k_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_845_, v_vals_846_, v_i_848_, v_k_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_851_, lean_object* v_keys_852_, lean_object* v_vals_853_, lean_object* v_heq_854_, lean_object* v_i_855_, lean_object* v_k_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(v_00_u03b2_851_, v_keys_852_, v_vals_853_, v_heq_854_, v_i_855_, v_k_856_);
lean_dec_ref(v_k_856_);
lean_dec_ref(v_vals_853_);
lean_dec_ref(v_keys_852_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_x_859_, v_x_860_, v_x_861_, v_x_862_);
return v___x_863_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Forall(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Forall(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_Main(builtin);
}
#ifdef __cplusplus
}
#endif
