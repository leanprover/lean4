// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Classify
// Imports: public import Lean.Meta.Sym.Arith.EvalNum import Lean.Meta.Sym.SynthInstance import Lean.Meta.Sym.Canon import Lean.Meta.DecLevel import Init.Grind.Ring
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
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_arithExt;
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IsCharP"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 211, 245, 119, 67, 24, 212, 73)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NoNatZeroDivisors"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 29, 6, 12, 7, 77, 98, 78)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(184, 238, 182, 216, 107, 45, 243, 168)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unexpected failure initializing ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_31_, v___y_35_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___boxed(lean_object* v_e_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(v_e_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(lean_object* v_k_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; 
lean_inc(v___y_51_);
lean_inc_ref(v___y_50_);
v___x_57_ = lean_apply_7(v_k_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, lean_box(0));
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_k_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(v_k_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(lean_object* v_k_67_, uint8_t v_allowLevelAssignments_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___f_76_; lean_object* v___x_77_; 
lean_inc(v___y_70_);
lean_inc_ref(v___y_69_);
v___f_76_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_76_, 0, v_k_67_);
lean_closure_set(v___f_76_, 1, v___y_69_);
lean_closure_set(v___f_76_, 2, v___y_70_);
v___x_77_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_68_, v___f_76_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
if (lean_obj_tag(v___x_77_) == 0)
{
return v___x_77_;
}
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(lean_object* v_k_86_, lean_object* v_allowLevelAssignments_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_95_; lean_object* v_res_96_; 
v_allowLevelAssignments_boxed_95_ = lean_unbox(v_allowLevelAssignments_87_);
v_res_96_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_86_, v_allowLevelAssignments_boxed_95_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(lean_object* v_00_u03b1_97_, lean_object* v_k_98_, uint8_t v_allowLevelAssignments_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_98_, v_allowLevelAssignments_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___boxed(lean_object* v_00_u03b1_108_, lean_object* v_k_109_, lean_object* v_allowLevelAssignments_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_118_; lean_object* v_res_119_; 
v_allowLevelAssignments_boxed_118_ = lean_unbox(v_allowLevelAssignments_110_);
v_res_119_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(v_00_u03b1_108_, v_k_109_, v_allowLevelAssignments_boxed_118_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(lean_object* v___x_127_, uint8_t v___x_128_, lean_object* v___x_129_, lean_object* v_u_130_, lean_object* v___x_131_, lean_object* v_type_132_, lean_object* v_semiringInst_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Meta_mkFreshExprMVar(v___x_127_, v___x_128_, v___x_129_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_charType_146_; lean_object* v___x_147_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc_n(v_a_142_, 2);
lean_dec_ref_known(v___x_141_, 1);
v___x_143_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3));
v___x_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_144_, 0, v_u_130_);
lean_ctor_set(v___x_144_, 1, v___x_131_);
v___x_145_ = l_Lean_mkConst(v___x_143_, v___x_144_);
v_charType_146_ = l_Lean_mkApp3(v___x_145_, v_type_132_, v_semiringInst_133_, v_a_142_);
v___x_147_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_charType_146_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_189_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_189_ == 0)
{
v___x_150_ = v___x_147_;
v_isShared_151_ = v_isSharedCheck_189_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_189_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
if (lean_obj_tag(v_a_148_) == 1)
{
lean_object* v_val_152_; lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v___x_155_; 
lean_del_object(v___x_150_);
v_val_152_ = lean_ctor_get(v_a_148_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v_a_148_, 1);
v___x_153_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_142_, v___y_137_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref(v___x_153_);
v___x_155_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(v_a_154_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_176_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_176_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_176_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_176_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
if (lean_obj_tag(v_a_156_) == 1)
{
lean_object* v_val_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_171_; 
v_val_160_ = lean_ctor_get(v_a_156_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v_a_156_);
if (v_isSharedCheck_171_ == 0)
{
v___x_162_ = v_a_156_;
v_isShared_163_ = v_isSharedCheck_171_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_val_160_);
lean_dec(v_a_156_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_171_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v_val_152_);
lean_ctor_set(v___x_164_, 1, v_val_160_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_170_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_166_);
v___x_168_ = v___x_158_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
else
{
lean_object* v___x_172_; lean_object* v___x_174_; 
lean_dec(v_a_156_);
lean_dec(v_val_152_);
v___x_172_ = lean_box(0);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_172_);
v___x_174_ = v___x_158_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_val_152_);
v_a_177_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_155_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_155_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
lean_object* v___x_185_; lean_object* v___x_187_; 
lean_dec(v_a_148_);
lean_dec(v_a_142_);
v___x_185_ = lean_box(0);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_185_);
v___x_187_ = v___x_150_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec(v_a_142_);
v_a_190_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_147_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_147_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec_ref(v_semiringInst_133_);
lean_dec_ref(v_type_132_);
lean_dec(v___x_131_);
lean_dec(v_u_130_);
v_a_198_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_141_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_141_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed(lean_object* v___x_206_, lean_object* v___x_207_, lean_object* v___x_208_, lean_object* v_u_209_, lean_object* v___x_210_, lean_object* v_type_211_, lean_object* v_semiringInst_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
uint8_t v___x_3813__boxed_220_; lean_object* v_res_221_; 
v___x_3813__boxed_220_ = lean_unbox(v___x_207_);
v_res_221_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(v___x_206_, v___x_3813__boxed_220_, v___x_208_, v_u_209_, v___x_210_, v_type_211_, v_semiringInst_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_box(0);
v___x_226_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1));
v___x_227_ = l_Lean_mkConst(v___x_226_, v___x_225_);
return v___x_227_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2);
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(lean_object* v_u_230_, lean_object* v_type_231_, lean_object* v_semiringInst_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___f_245_; uint8_t v___x_246_; lean_object* v___x_247_; 
v___x_240_ = lean_box(0);
v___x_241_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3);
v___x_242_ = 0;
v___x_243_ = lean_box(0);
v___x_244_ = lean_box(v___x_242_);
v___f_245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed), 14, 7);
lean_closure_set(v___f_245_, 0, v___x_241_);
lean_closure_set(v___f_245_, 1, v___x_244_);
lean_closure_set(v___f_245_, 2, v___x_243_);
lean_closure_set(v___f_245_, 3, v_u_230_);
lean_closure_set(v___f_245_, 4, v___x_240_);
lean_closure_set(v___f_245_, 5, v_type_231_);
lean_closure_set(v___f_245_, 6, v_semiringInst_232_);
v___x_246_ = 0;
v___x_247_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_245_, v___x_246_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___boxed(lean_object* v_u_248_, lean_object* v_type_249_, lean_object* v_semiringInst_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_u_248_, v_type_249_, v_semiringInst_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(lean_object* v_u_269_, lean_object* v_type_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_natModuleType_281_; lean_object* v___x_282_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1));
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v_u_269_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
lean_inc_ref(v___x_279_);
v___x_280_ = l_Lean_mkConst(v___x_277_, v___x_279_);
lean_inc_ref(v_type_270_);
v_natModuleType_281_ = l_Lean_Expr_app___override(v___x_280_, v_type_270_);
v___x_282_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_281_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_296_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_296_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_296_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_296_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
if (lean_obj_tag(v_a_283_) == 1)
{
lean_object* v_val_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_del_object(v___x_285_);
v_val_287_ = lean_ctor_get(v_a_283_, 0);
lean_inc(v_val_287_);
lean_dec_ref_known(v_a_283_, 1);
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3));
v___x_289_ = l_Lean_mkConst(v___x_288_, v___x_279_);
v___x_290_ = l_Lean_mkAppB(v___x_289_, v_type_270_, v_val_287_);
v___x_291_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_290_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec(v_a_283_);
lean_dec_ref_known(v___x_279_, 2);
lean_dec_ref(v_type_270_);
v___x_292_ = lean_box(0);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_292_);
v___x_294_ = v___x_285_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_279_, 2);
lean_dec_ref(v_type_270_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___boxed(lean_object* v_u_297_, lean_object* v_type_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_297_, v_type_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(lean_object* v_u_306_, lean_object* v_type_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_306_, v_type_307_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___boxed(lean_object* v_u_316_, lean_object* v_type_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(v_u_316_, v_type_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___lam__0(lean_object* v___x_326_, lean_object* v_s_327_){
_start:
{
lean_object* v_exp_328_; lean_object* v_rings_329_; lean_object* v_semirings_330_; lean_object* v_ncRings_331_; lean_object* v_ncSemirings_332_; lean_object* v_typeClassify_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_341_; 
v_exp_328_ = lean_ctor_get(v_s_327_, 0);
v_rings_329_ = lean_ctor_get(v_s_327_, 1);
v_semirings_330_ = lean_ctor_get(v_s_327_, 2);
v_ncRings_331_ = lean_ctor_get(v_s_327_, 3);
v_ncSemirings_332_ = lean_ctor_get(v_s_327_, 4);
v_typeClassify_333_ = lean_ctor_get(v_s_327_, 5);
v_isSharedCheck_341_ = !lean_is_exclusive(v_s_327_);
if (v_isSharedCheck_341_ == 0)
{
v___x_335_ = v_s_327_;
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_typeClassify_333_);
lean_inc(v_ncSemirings_332_);
lean_inc(v_ncRings_331_);
lean_inc(v_semirings_330_);
lean_inc(v_rings_329_);
lean_inc(v_exp_328_);
lean_dec(v_s_327_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_array_push(v_rings_329_, v___x_326_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v___x_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_exp_328_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_semirings_330_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v_ncRings_331_);
lean_ctor_set(v_reuseFailAlloc_340_, 4, v_ncSemirings_332_);
lean_ctor_set(v_reuseFailAlloc_340_, 5, v_typeClassify_333_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(lean_object* v_type_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
lean_inc_ref(v_type_371_);
v___x_379_ = l_Lean_Meta_getDecLevel(v_type_371_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc_n(v_a_380_, 2);
lean_dec_ref_known(v___x_379_, 1);
v___x_381_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1));
v___x_382_ = lean_box(0);
v___x_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_383_, 0, v_a_380_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
lean_inc_ref(v___x_383_);
v___x_384_ = l_Lean_mkConst(v___x_381_, v___x_383_);
lean_inc_ref(v_type_371_);
v___x_385_ = l_Lean_Expr_app___override(v___x_384_, v_type_371_);
v___x_386_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_385_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_479_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_479_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_479_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_479_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
if (lean_obj_tag(v_a_387_) == 1)
{
lean_object* v_val_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_474_; 
lean_del_object(v___x_389_);
v_val_391_ = lean_ctor_get(v_a_387_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_387_);
if (v_isSharedCheck_474_ == 0)
{
v___x_393_ = v_a_387_;
v_isShared_394_ = v_isSharedCheck_474_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_val_391_);
lean_dec(v_a_387_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_474_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3));
lean_inc_ref_n(v___x_383_, 3);
v___x_396_ = l_Lean_mkConst(v___x_395_, v___x_383_);
lean_inc(v_val_391_);
lean_inc_ref_n(v_type_371_, 4);
v___x_397_ = l_Lean_mkAppB(v___x_396_, v_type_371_, v_val_391_);
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6));
v___x_399_ = l_Lean_mkConst(v___x_398_, v___x_383_);
lean_inc_ref(v___x_397_);
v___x_400_ = l_Lean_mkAppB(v___x_399_, v_type_371_, v___x_397_);
v___x_401_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8));
v___x_402_ = l_Lean_mkConst(v___x_401_, v___x_383_);
lean_inc_ref_n(v___x_400_, 2);
v___x_403_ = l_Lean_mkAppB(v___x_402_, v_type_371_, v___x_400_);
lean_inc(v_a_380_);
v___x_404_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_a_380_, v_type_371_, v___x_400_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_406_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 1);
lean_inc_ref(v_type_371_);
lean_inc(v_a_380_);
v___x_406_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_a_380_, v_type_371_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10));
v___x_409_ = l_Lean_mkConst(v___x_408_, v___x_383_);
lean_inc_ref(v_type_371_);
v___x_410_ = l_Lean_Expr_app___override(v___x_409_, v_type_371_);
v___x_411_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_410_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_373_, v_a_376_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v_rings_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___f_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v_rings_415_ = lean_ctor_get(v_a_414_, 1);
lean_inc_ref(v_rings_415_);
lean_dec(v_a_414_);
v___x_416_ = lean_box(0);
v___x_417_ = lean_array_get_size(v_rings_415_);
lean_dec_ref(v_rings_415_);
v___x_418_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v_type_371_);
lean_ctor_set(v___x_418_, 2, v_a_380_);
lean_ctor_set(v___x_418_, 3, v___x_397_);
lean_ctor_set(v___x_418_, 4, v___x_400_);
lean_ctor_set(v___x_418_, 5, v_a_405_);
lean_ctor_set(v___x_418_, 6, v___x_416_);
lean_ctor_set(v___x_418_, 7, v___x_416_);
lean_ctor_set(v___x_418_, 8, v___x_416_);
lean_ctor_set(v___x_418_, 9, v___x_416_);
lean_ctor_set(v___x_418_, 10, v___x_416_);
lean_ctor_set(v___x_418_, 11, v___x_416_);
lean_ctor_set(v___x_418_, 12, v___x_416_);
lean_ctor_set(v___x_418_, 13, v___x_416_);
v___x_419_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_416_);
lean_ctor_set(v___x_419_, 2, v___x_416_);
lean_ctor_set(v___x_419_, 3, v___x_403_);
lean_ctor_set(v___x_419_, 4, v_val_391_);
lean_ctor_set(v___x_419_, 5, v_a_407_);
lean_ctor_set(v___x_419_, 6, v_a_412_);
v___f_420_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___lam__0), 2, 1);
lean_closure_set(v___f_420_, 0, v___x_419_);
v___x_421_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_422_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_421_, v___f_420_, v_a_373_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_432_; 
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v___x_422_, 0);
lean_dec(v_unused_433_);
v___x_424_ = v___x_422_;
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
else
{
lean_dec(v___x_422_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_417_);
v___x_427_ = v___x_393_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_417_);
v___x_427_ = v_reuseFailAlloc_431_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_429_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_427_);
v___x_429_ = v___x_424_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_del_object(v___x_393_);
v_a_434_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_422_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_422_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec(v_a_412_);
lean_dec(v_a_407_);
lean_dec(v_a_405_);
lean_dec_ref(v___x_403_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v___x_397_);
lean_del_object(v___x_393_);
lean_dec(v_val_391_);
lean_dec(v_a_380_);
lean_dec_ref(v_type_371_);
v_a_442_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_413_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_413_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_a_407_);
lean_dec(v_a_405_);
lean_dec_ref(v___x_403_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v___x_397_);
lean_del_object(v___x_393_);
lean_dec(v_val_391_);
lean_dec(v_a_380_);
lean_dec_ref(v_type_371_);
v_a_450_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_411_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_411_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
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
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec(v_a_405_);
lean_dec_ref(v___x_403_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v___x_397_);
lean_del_object(v___x_393_);
lean_dec(v_val_391_);
lean_dec_ref_known(v___x_383_, 2);
lean_dec(v_a_380_);
lean_dec_ref(v_type_371_);
v_a_458_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_406_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_406_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec_ref(v___x_403_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v___x_397_);
lean_del_object(v___x_393_);
lean_dec(v_val_391_);
lean_dec_ref_known(v___x_383_, 2);
lean_dec(v_a_380_);
lean_dec_ref(v_type_371_);
v_a_466_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_404_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_404_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec(v_a_387_);
lean_dec_ref_known(v___x_383_, 2);
lean_dec(v_a_380_);
lean_dec_ref(v_type_371_);
v___x_475_ = lean_box(0);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_475_);
v___x_477_ = v___x_389_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref_known(v___x_383_, 2);
lean_dec(v_a_380_);
lean_dec_ref(v_type_371_);
v_a_480_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_386_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_386_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_type_371_);
v_a_488_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_379_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_379_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___boxed(lean_object* v_type_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(lean_object* v___x_505_, lean_object* v_s_506_){
_start:
{
lean_object* v_exp_507_; lean_object* v_rings_508_; lean_object* v_semirings_509_; lean_object* v_ncRings_510_; lean_object* v_ncSemirings_511_; lean_object* v_typeClassify_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_520_; 
v_exp_507_ = lean_ctor_get(v_s_506_, 0);
v_rings_508_ = lean_ctor_get(v_s_506_, 1);
v_semirings_509_ = lean_ctor_get(v_s_506_, 2);
v_ncRings_510_ = lean_ctor_get(v_s_506_, 3);
v_ncSemirings_511_ = lean_ctor_get(v_s_506_, 4);
v_typeClassify_512_ = lean_ctor_get(v_s_506_, 5);
v_isSharedCheck_520_ = !lean_is_exclusive(v_s_506_);
if (v_isSharedCheck_520_ == 0)
{
v___x_514_ = v_s_506_;
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_typeClassify_512_);
lean_inc(v_ncSemirings_511_);
lean_inc(v_ncRings_510_);
lean_inc(v_semirings_509_);
lean_inc(v_rings_508_);
lean_inc(v_exp_507_);
lean_dec(v_s_506_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_array_push(v_ncRings_510_, v___x_505_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 3, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_exp_507_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_rings_508_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_semirings_509_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_ncSemirings_511_);
lean_ctor_set(v_reuseFailAlloc_519_, 5, v_typeClassify_512_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(lean_object* v_type_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v___x_533_; 
lean_inc_ref(v_type_525_);
v___x_533_ = l_Lean_Meta_getDecLevel(v_type_525_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc_n(v_a_534_, 2);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0));
v___x_536_ = lean_box(0);
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v_a_534_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
lean_inc_ref(v___x_537_);
v___x_538_ = l_Lean_mkConst(v___x_535_, v___x_537_);
lean_inc_ref(v_type_525_);
v___x_539_ = l_Lean_Expr_app___override(v___x_538_, v_type_525_);
v___x_540_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_539_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_603_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_603_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_603_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_603_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
if (lean_obj_tag(v_a_541_) == 1)
{
lean_object* v_val_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_598_; 
lean_del_object(v___x_543_);
v_val_545_ = lean_ctor_get(v_a_541_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_a_541_);
if (v_isSharedCheck_598_ == 0)
{
v___x_547_ = v_a_541_;
v_isShared_548_ = v_isSharedCheck_598_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_val_545_);
lean_dec(v_a_541_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_598_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6));
v___x_550_ = l_Lean_mkConst(v___x_549_, v___x_537_);
lean_inc(v_val_545_);
lean_inc_ref_n(v_type_525_, 2);
v___x_551_ = l_Lean_mkAppB(v___x_550_, v_type_525_, v_val_545_);
lean_inc_ref(v___x_551_);
lean_inc(v_a_534_);
v___x_552_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_a_534_, v_type_525_, v___x_551_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_527_, v_a_530_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v_ncRings_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___f_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v_ncRings_556_ = lean_ctor_get(v_a_555_, 3);
lean_inc_ref(v_ncRings_556_);
lean_dec(v_a_555_);
v___x_557_ = lean_array_get_size(v_ncRings_556_);
lean_dec_ref(v_ncRings_556_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v_type_525_);
lean_ctor_set(v___x_559_, 2, v_a_534_);
lean_ctor_set(v___x_559_, 3, v_val_545_);
lean_ctor_set(v___x_559_, 4, v___x_551_);
lean_ctor_set(v___x_559_, 5, v_a_553_);
lean_ctor_set(v___x_559_, 6, v___x_558_);
lean_ctor_set(v___x_559_, 7, v___x_558_);
lean_ctor_set(v___x_559_, 8, v___x_558_);
lean_ctor_set(v___x_559_, 9, v___x_558_);
lean_ctor_set(v___x_559_, 10, v___x_558_);
lean_ctor_set(v___x_559_, 11, v___x_558_);
lean_ctor_set(v___x_559_, 12, v___x_558_);
lean_ctor_set(v___x_559_, 13, v___x_558_);
v___f_560_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0), 2, 1);
lean_closure_set(v___f_560_, 0, v___x_559_);
v___x_561_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_562_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_561_, v___f_560_, v_a_527_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_572_; 
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v___x_562_, 0);
lean_dec(v_unused_573_);
v___x_564_ = v___x_562_;
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
else
{
lean_dec(v___x_562_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_557_);
v___x_567_ = v___x_547_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_557_);
v___x_567_ = v_reuseFailAlloc_571_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_567_);
v___x_569_ = v___x_564_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_del_object(v___x_547_);
v_a_574_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_562_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_562_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec(v_a_553_);
lean_dec_ref(v___x_551_);
lean_del_object(v___x_547_);
lean_dec(v_val_545_);
lean_dec(v_a_534_);
lean_dec_ref(v_type_525_);
v_a_582_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_554_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_554_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v___x_551_);
lean_del_object(v___x_547_);
lean_dec(v_val_545_);
lean_dec(v_a_534_);
lean_dec_ref(v_type_525_);
v_a_590_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_552_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_552_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_601_; 
lean_dec(v_a_541_);
lean_dec_ref_known(v___x_537_, 2);
lean_dec(v_a_534_);
lean_dec_ref(v_type_525_);
v___x_599_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_599_);
v___x_601_ = v___x_543_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref_known(v___x_537_, 2);
lean_dec(v_a_534_);
lean_dec_ref(v_type_525_);
v_a_604_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_540_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_540_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_type_525_);
v_a_612_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_533_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_533_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___boxed(lean_object* v_type_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
lean_object* v_ks_633_; lean_object* v_vs_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_658_; 
v_ks_633_ = lean_ctor_get(v_x_629_, 0);
v_vs_634_ = lean_ctor_get(v_x_629_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_629_);
if (v_isSharedCheck_658_ == 0)
{
v___x_636_ = v_x_629_;
v_isShared_637_ = v_isSharedCheck_658_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_vs_634_);
lean_inc(v_ks_633_);
lean_dec(v_x_629_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_658_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_array_get_size(v_ks_633_);
v___x_639_ = lean_nat_dec_lt(v_x_630_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
lean_dec(v_x_630_);
v___x_640_ = lean_array_push(v_ks_633_, v_x_631_);
v___x_641_ = lean_array_push(v_vs_634_, v_x_632_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_641_);
lean_ctor_set(v___x_636_, 0, v___x_640_);
v___x_643_ = v___x_636_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
else
{
lean_object* v_k_x27_645_; uint8_t v___x_646_; 
v_k_x27_645_ = lean_array_fget_borrowed(v_ks_633_, v_x_630_);
v___x_646_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_631_, v_k_x27_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_648_; 
if (v_isShared_637_ == 0)
{
v___x_648_ = v___x_636_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_ks_633_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_vs_634_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_x_630_, v___x_649_);
lean_dec(v_x_630_);
v_x_629_ = v___x_648_;
v_x_630_ = v___x_650_;
goto _start;
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_653_ = lean_array_fset(v_ks_633_, v_x_630_, v_x_631_);
v___x_654_ = lean_array_fset(v_vs_634_, v_x_630_, v_x_632_);
lean_dec(v_x_630_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_654_);
lean_ctor_set(v___x_636_, 0, v___x_653_);
v___x_656_ = v___x_636_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_659_, lean_object* v_k_660_, lean_object* v_v_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_659_, v___x_662_, v_k_660_, v_v_661_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(lean_object* v_x_665_, size_t v_x_666_, size_t v_x_667_, lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_665_) == 0)
{
lean_object* v_es_670_; size_t v___x_671_; size_t v___x_672_; lean_object* v_j_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_es_670_ = lean_ctor_get(v_x_665_, 0);
v___x_671_ = ((size_t)31ULL);
v___x_672_ = lean_usize_land(v_x_666_, v___x_671_);
v_j_673_ = lean_usize_to_nat(v___x_672_);
v___x_674_ = lean_array_get_size(v_es_670_);
v___x_675_ = lean_nat_dec_lt(v_j_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_dec(v_j_673_);
lean_dec(v_x_669_);
lean_dec_ref(v_x_668_);
return v_x_665_;
}
else
{
lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_714_; 
lean_inc_ref(v_es_670_);
v_isSharedCheck_714_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_x_665_, 0);
lean_dec(v_unused_715_);
v___x_677_ = v_x_665_;
v_isShared_678_ = v_isSharedCheck_714_;
goto v_resetjp_676_;
}
else
{
lean_dec(v_x_665_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_714_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_v_679_; lean_object* v___x_680_; lean_object* v_xs_x27_681_; lean_object* v___y_683_; 
v_v_679_ = lean_array_fget(v_es_670_, v_j_673_);
v___x_680_ = lean_box(0);
v_xs_x27_681_ = lean_array_fset(v_es_670_, v_j_673_, v___x_680_);
switch(lean_obj_tag(v_v_679_))
{
case 0:
{
lean_object* v_key_688_; lean_object* v_val_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_699_; 
v_key_688_ = lean_ctor_get(v_v_679_, 0);
v_val_689_ = lean_ctor_get(v_v_679_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_v_679_);
if (v_isSharedCheck_699_ == 0)
{
v___x_691_ = v_v_679_;
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_val_689_);
lean_inc(v_key_688_);
lean_dec(v_v_679_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; 
v___x_693_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_668_, v_key_688_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_del_object(v___x_691_);
v___x_694_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_688_, v_val_689_, v_x_668_, v_x_669_);
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
v___y_683_ = v___x_695_;
goto v___jp_682_;
}
else
{
lean_object* v___x_697_; 
lean_dec(v_val_689_);
lean_dec(v_key_688_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_x_669_);
lean_ctor_set(v___x_691_, 0, v_x_668_);
v___x_697_ = v___x_691_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_x_668_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_x_669_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v___y_683_ = v___x_697_;
goto v___jp_682_;
}
}
}
}
case 1:
{
lean_object* v_node_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_712_; 
v_node_700_ = lean_ctor_get(v_v_679_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v_v_679_);
if (v_isSharedCheck_712_ == 0)
{
v___x_702_ = v_v_679_;
v_isShared_703_ = v_isSharedCheck_712_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_node_700_);
lean_dec(v_v_679_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_712_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
size_t v___x_704_; size_t v___x_705_; size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_704_ = ((size_t)5ULL);
v___x_705_ = lean_usize_shift_right(v_x_666_, v___x_704_);
v___x_706_ = ((size_t)1ULL);
v___x_707_ = lean_usize_add(v_x_667_, v___x_706_);
v___x_708_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_node_700_, v___x_705_, v___x_707_, v_x_668_, v_x_669_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_708_);
v___x_710_ = v___x_702_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
v___y_683_ = v___x_710_;
goto v___jp_682_;
}
}
}
default: 
{
lean_object* v___x_713_; 
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_x_668_);
lean_ctor_set(v___x_713_, 1, v_x_669_);
v___y_683_ = v___x_713_;
goto v___jp_682_;
}
}
v___jp_682_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = lean_array_fset(v_xs_x27_681_, v_j_673_, v___y_683_);
lean_dec(v_j_673_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_684_);
v___x_686_ = v___x_677_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
else
{
lean_object* v_ks_716_; lean_object* v_vs_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_737_; 
v_ks_716_ = lean_ctor_get(v_x_665_, 0);
v_vs_717_ = lean_ctor_get(v_x_665_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_737_ == 0)
{
v___x_719_ = v_x_665_;
v_isShared_720_ = v_isSharedCheck_737_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_vs_717_);
lean_inc(v_ks_716_);
lean_dec(v_x_665_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_737_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_ks_716_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_vs_717_);
v___x_722_ = v_reuseFailAlloc_736_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v_newNode_723_; uint8_t v___y_725_; size_t v___x_731_; uint8_t v___x_732_; 
v_newNode_723_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v___x_722_, v_x_668_, v_x_669_);
v___x_731_ = ((size_t)7ULL);
v___x_732_ = lean_usize_dec_le(v___x_731_, v_x_667_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_733_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_723_);
v___x_734_ = lean_unsigned_to_nat(4u);
v___x_735_ = lean_nat_dec_lt(v___x_733_, v___x_734_);
lean_dec(v___x_733_);
v___y_725_ = v___x_735_;
goto v___jp_724_;
}
else
{
v___y_725_ = v___x_732_;
goto v___jp_724_;
}
v___jp_724_:
{
if (v___y_725_ == 0)
{
lean_object* v_ks_726_; lean_object* v_vs_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_ks_726_ = lean_ctor_get(v_newNode_723_, 0);
lean_inc_ref(v_ks_726_);
v_vs_727_ = lean_ctor_get(v_newNode_723_, 1);
lean_inc_ref(v_vs_727_);
lean_dec_ref(v_newNode_723_);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0);
v___x_730_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_x_667_, v_ks_726_, v_vs_727_, v___x_728_, v___x_729_);
lean_dec_ref(v_vs_727_);
lean_dec_ref(v_ks_726_);
return v___x_730_;
}
else
{
return v_newNode_723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_738_, lean_object* v_keys_739_, lean_object* v_vals_740_, lean_object* v_i_741_, lean_object* v_entries_742_){
_start:
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_array_get_size(v_keys_739_);
v___x_744_ = lean_nat_dec_lt(v_i_741_, v___x_743_);
if (v___x_744_ == 0)
{
lean_dec(v_i_741_);
return v_entries_742_;
}
else
{
lean_object* v_k_745_; lean_object* v_v_746_; uint64_t v___x_747_; size_t v_h_748_; size_t v___x_749_; lean_object* v___x_750_; size_t v___x_751_; size_t v___x_752_; size_t v___x_753_; size_t v_h_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_k_745_ = lean_array_fget_borrowed(v_keys_739_, v_i_741_);
v_v_746_ = lean_array_fget_borrowed(v_vals_740_, v_i_741_);
v___x_747_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_745_);
v_h_748_ = lean_uint64_to_usize(v___x_747_);
v___x_749_ = ((size_t)5ULL);
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = ((size_t)1ULL);
v___x_752_ = lean_usize_sub(v_depth_738_, v___x_751_);
v___x_753_ = lean_usize_mul(v___x_749_, v___x_752_);
v_h_754_ = lean_usize_shift_right(v_h_748_, v___x_753_);
v___x_755_ = lean_nat_add(v_i_741_, v___x_750_);
lean_dec(v_i_741_);
lean_inc(v_v_746_);
lean_inc(v_k_745_);
v___x_756_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_entries_742_, v_h_754_, v_depth_738_, v_k_745_, v_v_746_);
v_i_741_ = v___x_755_;
v_entries_742_ = v___x_756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_758_, lean_object* v_keys_759_, lean_object* v_vals_760_, lean_object* v_i_761_, lean_object* v_entries_762_){
_start:
{
size_t v_depth_boxed_763_; lean_object* v_res_764_; 
v_depth_boxed_763_ = lean_unbox_usize(v_depth_758_);
lean_dec(v_depth_758_);
v_res_764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_763_, v_keys_759_, v_vals_760_, v_i_761_, v_entries_762_);
lean_dec_ref(v_vals_760_);
lean_dec_ref(v_keys_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
size_t v_x_2068__boxed_770_; size_t v_x_2069__boxed_771_; lean_object* v_res_772_; 
v_x_2068__boxed_770_ = lean_unbox_usize(v_x_766_);
lean_dec(v_x_766_);
v_x_2069__boxed_771_ = lean_unbox_usize(v_x_767_);
lean_dec(v_x_767_);
v_res_772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_765_, v_x_2068__boxed_770_, v_x_2069__boxed_771_, v_x_768_, v_x_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
uint64_t v___x_776_; size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
v___x_776_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_774_);
v___x_777_ = lean_uint64_to_usize(v___x_776_);
v___x_778_ = ((size_t)1ULL);
v___x_779_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_773_, v___x_777_, v___x_778_, v_x_774_, v_x_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(lean_object* v_type_780_, lean_object* v___y_781_, lean_object* v_s_782_){
_start:
{
lean_object* v_exp_783_; lean_object* v_rings_784_; lean_object* v_semirings_785_; lean_object* v_ncRings_786_; lean_object* v_ncSemirings_787_; lean_object* v_typeClassify_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_exp_783_ = lean_ctor_get(v_s_782_, 0);
v_rings_784_ = lean_ctor_get(v_s_782_, 1);
v_semirings_785_ = lean_ctor_get(v_s_782_, 2);
v_ncRings_786_ = lean_ctor_get(v_s_782_, 3);
v_ncSemirings_787_ = lean_ctor_get(v_s_782_, 4);
v_typeClassify_788_ = lean_ctor_get(v_s_782_, 5);
v_isSharedCheck_796_ = !lean_is_exclusive(v_s_782_);
if (v_isSharedCheck_796_ == 0)
{
v___x_790_ = v_s_782_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_typeClassify_788_);
lean_inc(v_ncSemirings_787_);
lean_inc(v_ncRings_786_);
lean_inc(v_semirings_785_);
lean_inc(v_rings_784_);
lean_inc(v_exp_783_);
lean_dec(v_s_782_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_788_, v_type_780_, v___y_781_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 5, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_exp_783_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_rings_784_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_semirings_785_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_ncRings_786_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_ncSemirings_787_);
lean_ctor_set(v_reuseFailAlloc_795_, 5, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_797_, lean_object* v_vals_798_, lean_object* v_i_799_, lean_object* v_k_800_){
_start:
{
lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_801_ = lean_array_get_size(v_keys_797_);
v___x_802_ = lean_nat_dec_lt(v_i_799_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
lean_dec(v_i_799_);
v___x_803_ = lean_box(0);
return v___x_803_;
}
else
{
lean_object* v_k_x27_804_; uint8_t v___x_805_; 
v_k_x27_804_ = lean_array_fget_borrowed(v_keys_797_, v_i_799_);
v___x_805_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_800_, v_k_x27_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_i_799_, v___x_806_);
lean_dec(v_i_799_);
v_i_799_ = v___x_807_;
goto _start;
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_array_fget_borrowed(v_vals_798_, v_i_799_);
lean_dec(v_i_799_);
lean_inc(v___x_809_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_811_, lean_object* v_vals_812_, lean_object* v_i_813_, lean_object* v_k_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_811_, v_vals_812_, v_i_813_, v_k_814_);
lean_dec_ref(v_k_814_);
lean_dec_ref(v_vals_812_);
lean_dec_ref(v_keys_811_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(lean_object* v_x_816_, size_t v_x_817_, lean_object* v_x_818_){
_start:
{
if (lean_obj_tag(v_x_816_) == 0)
{
lean_object* v_es_819_; lean_object* v___x_820_; size_t v___x_821_; size_t v___x_822_; lean_object* v_j_823_; lean_object* v___x_824_; 
v_es_819_ = lean_ctor_get(v_x_816_, 0);
v___x_820_ = lean_box(2);
v___x_821_ = ((size_t)31ULL);
v___x_822_ = lean_usize_land(v_x_817_, v___x_821_);
v_j_823_ = lean_usize_to_nat(v___x_822_);
v___x_824_ = lean_array_get_borrowed(v___x_820_, v_es_819_, v_j_823_);
lean_dec(v_j_823_);
switch(lean_obj_tag(v___x_824_))
{
case 0:
{
lean_object* v_key_825_; lean_object* v_val_826_; uint8_t v___x_827_; 
v_key_825_ = lean_ctor_get(v___x_824_, 0);
v_val_826_ = lean_ctor_get(v___x_824_, 1);
v___x_827_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_818_, v_key_825_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
v___x_828_ = lean_box(0);
return v___x_828_;
}
else
{
lean_object* v___x_829_; 
lean_inc(v_val_826_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v_val_826_);
return v___x_829_;
}
}
case 1:
{
lean_object* v_node_830_; size_t v___x_831_; size_t v___x_832_; 
v_node_830_ = lean_ctor_get(v___x_824_, 0);
v___x_831_ = ((size_t)5ULL);
v___x_832_ = lean_usize_shift_right(v_x_817_, v___x_831_);
v_x_816_ = v_node_830_;
v_x_817_ = v___x_832_;
goto _start;
}
default: 
{
lean_object* v___x_834_; 
v___x_834_ = lean_box(0);
return v___x_834_;
}
}
}
else
{
lean_object* v_ks_835_; lean_object* v_vs_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_ks_835_ = lean_ctor_get(v_x_816_, 0);
v_vs_836_ = lean_ctor_get(v_x_816_, 1);
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_ks_835_, v_vs_836_, v___x_837_, v_x_818_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
size_t v_x_2274__boxed_842_; lean_object* v_res_843_; 
v_x_2274__boxed_842_ = lean_unbox_usize(v_x_840_);
lean_dec(v_x_840_);
v_res_843_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_839_, v_x_2274__boxed_842_, v_x_841_);
lean_dec_ref(v_x_841_);
lean_dec_ref(v_x_839_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
uint64_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; 
v___x_846_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_845_);
v___x_847_ = lean_uint64_to_usize(v___x_846_);
v___x_848_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_844_, v___x_847_, v_x_845_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_849_, v_x_850_);
lean_dec_ref(v_x_850_);
lean_dec_ref(v_x_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(lean_object* v_type_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_854_, v_a_857_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_915_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_915_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_915_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_915_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_typeClassify_865_; lean_object* v___x_866_; 
v_typeClassify_865_ = lean_ctor_get(v_a_861_, 5);
lean_inc_ref(v_typeClassify_865_);
lean_dec(v_a_861_);
v___x_866_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_865_, v_type_852_);
lean_dec_ref(v_typeClassify_865_);
if (lean_obj_tag(v___x_866_) == 1)
{
lean_object* v_val_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref(v_type_852_);
v_val_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_882_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_882_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_val_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_882_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_val_867_) == 0)
{
lean_object* v_id_871_; lean_object* v___x_873_; 
v_id_871_ = lean_ctor_get(v_val_867_, 0);
lean_inc(v_id_871_);
lean_dec_ref_known(v_val_867_, 1);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_id_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_id_871_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_873_);
v___x_875_ = v___x_863_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
else
{
lean_object* v___x_878_; lean_object* v___x_880_; 
lean_del_object(v___x_869_);
lean_dec(v_val_867_);
v___x_878_ = lean_box(0);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_878_);
v___x_880_ = v___x_863_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v___x_883_; 
lean_dec(v___x_866_);
lean_del_object(v___x_863_);
lean_inc_ref(v_type_852_);
v___x_883_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_914_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_914_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_914_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_914_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___y_889_; 
if (lean_obj_tag(v_a_884_) == 0)
{
lean_object* v___x_909_; 
lean_del_object(v___x_886_);
v___x_909_ = lean_box(4);
v___y_889_ = v___x_909_;
goto v___jp_888_;
}
else
{
lean_object* v_val_910_; lean_object* v___x_912_; 
v_val_910_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_val_910_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_val_910_);
v___x_912_ = v___x_886_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_val_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
v___y_889_ = v___x_912_;
goto v___jp_888_;
}
}
v___jp_888_:
{
lean_object* v___f_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___f_890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0), 3, 2);
lean_closure_set(v___f_890_, 0, v_type_852_);
lean_closure_set(v___f_890_, 1, v___y_889_);
v___x_891_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_892_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_891_, v___f_890_, v_a_854_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v___x_892_, 0);
lean_dec(v_unused_900_);
v___x_894_ = v___x_892_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_dec(v___x_892_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_a_884_);
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_884_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_a_884_);
v_a_901_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_892_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_892_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_type_852_);
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v_type_852_);
v_a_916_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_860_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_860_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___boxed(lean_object* v_type_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_type_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(lean_object* v_00_u03b2_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_934_, v_x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(v_00_u03b2_937_, v_x_938_, v_x_939_);
lean_dec_ref(v_x_939_);
lean_dec_ref(v_x_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(lean_object* v_00_u03b2_941_, lean_object* v_x_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_x_942_, v_x_943_, v_x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(lean_object* v_00_u03b2_946_, lean_object* v_x_947_, size_t v_x_948_, lean_object* v_x_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_947_, v_x_948_, v_x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
size_t v_x_2480__boxed_955_; lean_object* v_res_956_; 
v_x_2480__boxed_955_ = lean_unbox_usize(v_x_953_);
lean_dec(v_x_953_);
v_res_956_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(v_00_u03b2_951_, v_x_952_, v_x_2480__boxed_955_, v_x_954_);
lean_dec_ref(v_x_954_);
lean_dec_ref(v_x_952_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(lean_object* v_00_u03b2_957_, lean_object* v_x_958_, size_t v_x_959_, size_t v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_958_, v_x_959_, v_x_960_, v_x_961_, v_x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
size_t v_x_2491__boxed_970_; size_t v_x_2492__boxed_971_; lean_object* v_res_972_; 
v_x_2491__boxed_970_ = lean_unbox_usize(v_x_966_);
lean_dec(v_x_966_);
v_x_2492__boxed_971_ = lean_unbox_usize(v_x_967_);
lean_dec(v_x_967_);
v_res_972_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(v_00_u03b2_964_, v_x_965_, v_x_2491__boxed_970_, v_x_2492__boxed_971_, v_x_968_, v_x_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_973_, lean_object* v_keys_974_, lean_object* v_vals_975_, lean_object* v_heq_976_, lean_object* v_i_977_, lean_object* v_k_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_974_, v_vals_975_, v_i_977_, v_k_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_980_, lean_object* v_keys_981_, lean_object* v_vals_982_, lean_object* v_heq_983_, lean_object* v_i_984_, lean_object* v_k_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(v_00_u03b2_980_, v_keys_981_, v_vals_982_, v_heq_983_, v_i_984_, v_k_985_);
lean_dec_ref(v_k_985_);
lean_dec_ref(v_vals_982_);
lean_dec_ref(v_keys_981_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_987_, lean_object* v_n_988_, lean_object* v_k_989_, lean_object* v_v_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v_n_988_, v_k_989_, v_v_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_992_, size_t v_depth_993_, lean_object* v_keys_994_, lean_object* v_vals_995_, lean_object* v_heq_996_, lean_object* v_i_997_, lean_object* v_entries_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_993_, v_keys_994_, v_vals_995_, v_i_997_, v_entries_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1000_, lean_object* v_depth_1001_, lean_object* v_keys_1002_, lean_object* v_vals_1003_, lean_object* v_heq_1004_, lean_object* v_i_1005_, lean_object* v_entries_1006_){
_start:
{
size_t v_depth_boxed_1007_; lean_object* v_res_1008_; 
v_depth_boxed_1007_ = lean_unbox_usize(v_depth_1001_);
lean_dec(v_depth_1001_);
v_res_1008_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1000_, v_depth_boxed_1007_, v_keys_1002_, v_vals_1003_, v_heq_1004_, v_i_1005_, v_entries_1006_);
lean_dec_ref(v_vals_1003_);
lean_dec_ref(v_keys_1002_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1010_, v_x_1011_, v_x_1012_, v_x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(lean_object* v___x_1015_, lean_object* v_s_1016_){
_start:
{
lean_object* v_exp_1017_; lean_object* v_rings_1018_; lean_object* v_semirings_1019_; lean_object* v_ncRings_1020_; lean_object* v_ncSemirings_1021_; lean_object* v_typeClassify_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_exp_1017_ = lean_ctor_get(v_s_1016_, 0);
v_rings_1018_ = lean_ctor_get(v_s_1016_, 1);
v_semirings_1019_ = lean_ctor_get(v_s_1016_, 2);
v_ncRings_1020_ = lean_ctor_get(v_s_1016_, 3);
v_ncSemirings_1021_ = lean_ctor_get(v_s_1016_, 4);
v_typeClassify_1022_ = lean_ctor_get(v_s_1016_, 5);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_s_1016_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v_s_1016_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_typeClassify_1022_);
lean_inc(v_ncSemirings_1021_);
lean_inc(v_ncRings_1020_);
lean_inc(v_semirings_1019_);
lean_inc(v_rings_1018_);
lean_inc(v_exp_1017_);
lean_dec(v_s_1016_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_array_push(v_semirings_1019_, v___x_1015_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 2, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_exp_1017_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_rings_1018_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_ncRings_1020_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_ncSemirings_1021_);
lean_ctor_set(v_reuseFailAlloc_1029_, 5, v_typeClassify_1022_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(lean_object* v_val_1031_, lean_object* v___x_1032_, lean_object* v_s_1033_){
_start:
{
lean_object* v_exp_1034_; lean_object* v_rings_1035_; lean_object* v_semirings_1036_; lean_object* v_ncRings_1037_; lean_object* v_ncSemirings_1038_; lean_object* v_typeClassify_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_exp_1034_ = lean_ctor_get(v_s_1033_, 0);
v_rings_1035_ = lean_ctor_get(v_s_1033_, 1);
v_semirings_1036_ = lean_ctor_get(v_s_1033_, 2);
v_ncRings_1037_ = lean_ctor_get(v_s_1033_, 3);
v_ncSemirings_1038_ = lean_ctor_get(v_s_1033_, 4);
v_typeClassify_1039_ = lean_ctor_get(v_s_1033_, 5);
v___x_1040_ = lean_array_get_size(v_rings_1035_);
v___x_1041_ = lean_nat_dec_lt(v_val_1031_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_dec(v___x_1032_);
return v_s_1033_;
}
else
{
lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1067_; 
lean_inc_ref(v_typeClassify_1039_);
lean_inc_ref(v_ncSemirings_1038_);
lean_inc_ref(v_ncRings_1037_);
lean_inc_ref(v_semirings_1036_);
lean_inc_ref(v_rings_1035_);
lean_inc(v_exp_1034_);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_s_1033_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; lean_object* v_unused_1069_; lean_object* v_unused_1070_; lean_object* v_unused_1071_; lean_object* v_unused_1072_; lean_object* v_unused_1073_; 
v_unused_1068_ = lean_ctor_get(v_s_1033_, 5);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_s_1033_, 4);
lean_dec(v_unused_1069_);
v_unused_1070_ = lean_ctor_get(v_s_1033_, 3);
lean_dec(v_unused_1070_);
v_unused_1071_ = lean_ctor_get(v_s_1033_, 2);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_s_1033_, 1);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_s_1033_, 0);
lean_dec(v_unused_1073_);
v___x_1043_ = v_s_1033_;
v_isShared_1044_ = v_isSharedCheck_1067_;
goto v_resetjp_1042_;
}
else
{
lean_dec(v_s_1033_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1067_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_v_1045_; lean_object* v_toRing_1046_; lean_object* v_invFn_x3f_1047_; lean_object* v_commSemiringInst_1048_; lean_object* v_commRingInst_1049_; lean_object* v_noZeroDivInst_x3f_1050_; lean_object* v_fieldInst_x3f_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1065_; 
v_v_1045_ = lean_array_fget(v_rings_1035_, v_val_1031_);
v_toRing_1046_ = lean_ctor_get(v_v_1045_, 0);
v_invFn_x3f_1047_ = lean_ctor_get(v_v_1045_, 1);
v_commSemiringInst_1048_ = lean_ctor_get(v_v_1045_, 3);
v_commRingInst_1049_ = lean_ctor_get(v_v_1045_, 4);
v_noZeroDivInst_x3f_1050_ = lean_ctor_get(v_v_1045_, 5);
v_fieldInst_x3f_1051_ = lean_ctor_get(v_v_1045_, 6);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_v_1045_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v_v_1045_, 2);
lean_dec(v_unused_1066_);
v___x_1053_ = v_v_1045_;
v_isShared_1054_ = v_isSharedCheck_1065_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_fieldInst_x3f_1051_);
lean_inc(v_noZeroDivInst_x3f_1050_);
lean_inc(v_commRingInst_1049_);
lean_inc(v_commSemiringInst_1048_);
lean_inc(v_invFn_x3f_1047_);
lean_inc(v_toRing_1046_);
lean_dec(v_v_1045_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1065_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v_xs_x27_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1055_ = lean_box(0);
v_xs_x27_1056_ = lean_array_fset(v_rings_1035_, v_val_1031_, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1032_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 2, v___x_1057_);
v___x_1059_ = v___x_1053_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_toRing_1046_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_invFn_x3f_1047_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_commSemiringInst_1048_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v_commRingInst_1049_);
lean_ctor_set(v_reuseFailAlloc_1064_, 5, v_noZeroDivInst_x3f_1050_);
lean_ctor_set(v_reuseFailAlloc_1064_, 6, v_fieldInst_x3f_1051_);
v___x_1059_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = lean_array_fset(v_xs_x27_1056_, v_val_1031_, v___x_1059_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___x_1060_);
v___x_1062_ = v___x_1043_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_exp_1034_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_semirings_1036_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_ncRings_1037_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v_ncSemirings_1038_);
lean_ctor_set(v_reuseFailAlloc_1063_, 5, v_typeClassify_1039_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1___boxed(lean_object* v_val_1074_, lean_object* v___x_1075_, lean_object* v_s_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(v_val_1074_, v___x_1075_, v_s_1076_);
lean_dec(v_val_1074_);
return v_res_1077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(lean_object* v_type_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1110_; 
lean_inc_ref(v_type_1099_);
v___x_1110_ = l_Lean_Meta_getDecLevel(v_type_1099_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_n(v_a_1111_, 2);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1112_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1));
v___x_1113_ = lean_box(0);
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_a_1111_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
lean_inc_ref(v___x_1114_);
v___x_1115_ = l_Lean_mkConst(v___x_1112_, v___x_1114_);
lean_inc_ref(v_type_1099_);
v___x_1116_ = l_Lean_Expr_app___override(v___x_1115_, v_type_1099_);
v___x_1117_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1116_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1230_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1230_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1230_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
if (lean_obj_tag(v_a_1118_) == 1)
{
lean_object* v_val_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_del_object(v___x_1120_);
v_val_1122_ = lean_ctor_get(v_a_1118_, 0);
lean_inc_n(v_val_1122_, 2);
lean_dec_ref_known(v_a_1118_, 1);
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2));
lean_inc_ref(v___x_1114_);
v___x_1124_ = l_Lean_mkConst(v___x_1123_, v___x_1114_);
lean_inc_ref_n(v_type_1099_, 2);
v___x_1125_ = l_Lean_mkAppB(v___x_1124_, v_type_1099_, v_val_1122_);
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5));
v___x_1127_ = l_Lean_mkConst(v___x_1126_, v___x_1114_);
lean_inc_ref(v___x_1125_);
v___x_1128_ = l_Lean_mkAppB(v___x_1127_, v_type_1099_, v___x_1125_);
v___x_1129_ = l_Lean_Meta_Sym_canon(v___x_1128_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = l_Lean_Meta_Sym_shareCommon(v_a_1130_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1133_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc_n(v_a_1132_, 2);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_a_1132_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
if (lean_obj_tag(v_a_1134_) == 1)
{
lean_object* v_val_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_a_1132_);
v_val_1135_ = lean_ctor_get(v_a_1134_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_a_1134_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1137_ = v_a_1134_;
v_isShared_1138_ = v_isSharedCheck_1186_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_val_1135_);
lean_dec(v_a_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1186_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1101_, v_a_1104_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v_semirings_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v_semirings_1141_ = lean_ctor_get(v_a_1140_, 2);
lean_inc_ref(v_semirings_1141_);
lean_dec(v_a_1140_);
v___x_1142_ = lean_array_get_size(v_semirings_1141_);
lean_dec_ref(v_semirings_1141_);
v___x_1143_ = lean_box(0);
v___x_1144_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v_type_1099_);
lean_ctor_set(v___x_1144_, 2, v_a_1111_);
lean_ctor_set(v___x_1144_, 3, v___x_1125_);
lean_ctor_set(v___x_1144_, 4, v___x_1143_);
lean_ctor_set(v___x_1144_, 5, v___x_1143_);
lean_ctor_set(v___x_1144_, 6, v___x_1143_);
lean_ctor_set(v___x_1144_, 7, v___x_1143_);
lean_inc(v_val_1135_);
v___x_1145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v_val_1135_);
lean_ctor_set(v___x_1145_, 2, v_val_1122_);
lean_ctor_set(v___x_1145_, 3, v___x_1143_);
lean_ctor_set(v___x_1145_, 4, v___x_1143_);
v___f_1146_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1146_, 0, v___x_1145_);
v___x_1147_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1148_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1147_, v___f_1146_, v_a_1101_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___f_1149_; lean_object* v___x_1150_; 
lean_dec_ref_known(v___x_1148_, 1);
v___f_1149_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1149_, 0, v_val_1135_);
lean_closure_set(v___f_1149_, 1, v___x_1142_);
v___x_1150_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1147_, v___f_1149_, v_a_1101_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1160_; 
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1150_, 0);
lean_dec(v_unused_1161_);
v___x_1152_ = v___x_1150_;
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
else
{
lean_dec(v___x_1150_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1142_);
v___x_1155_ = v___x_1137_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1142_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_del_object(v___x_1137_);
v_a_1162_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1150_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1150_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_del_object(v___x_1137_);
lean_dec(v_val_1135_);
v_a_1170_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1148_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1148_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_del_object(v___x_1137_);
lean_dec(v_val_1135_);
lean_dec_ref(v___x_1125_);
lean_dec(v_val_1122_);
lean_dec(v_a_1111_);
lean_dec_ref(v_type_1099_);
v_a_1178_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1139_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1139_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
else
{
lean_object* v___x_1187_; 
lean_dec(v_a_1134_);
lean_dec_ref(v___x_1125_);
lean_dec(v_val_1122_);
lean_dec(v_a_1111_);
lean_dec_ref(v_type_1099_);
v___x_1187_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1100_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; uint8_t v_verbose_1189_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v_verbose_1189_ = lean_ctor_get_uint8(v_a_1188_, 0);
lean_dec(v_a_1188_);
if (v_verbose_1189_ == 0)
{
lean_dec(v_a_1132_);
goto v___jp_1107_;
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1190_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7);
v___x_1191_ = l_Lean_indentExpr(v_a_1132_);
v___x_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_Meta_Sym_reportIssue(v___x_1192_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_dec_ref_known(v___x_1193_, 1);
goto v___jp_1107_;
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_a_1132_);
v_a_1202_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1187_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1187_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
else
{
lean_dec(v_a_1132_);
lean_dec_ref(v___x_1125_);
lean_dec(v_val_1122_);
lean_dec(v_a_1111_);
lean_dec_ref(v_type_1099_);
return v___x_1133_;
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v___x_1125_);
lean_dec(v_val_1122_);
lean_dec(v_a_1111_);
lean_dec_ref(v_type_1099_);
v_a_1210_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1131_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1131_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v___x_1125_);
lean_dec(v_val_1122_);
lean_dec(v_a_1111_);
lean_dec_ref(v_type_1099_);
v_a_1218_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1129_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1129_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
lean_dec(v_a_1118_);
lean_dec_ref_known(v___x_1114_, 2);
lean_dec(v_a_1111_);
lean_dec_ref(v_type_1099_);
v___x_1226_ = lean_box(0);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1226_);
v___x_1228_ = v___x_1120_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec_ref_known(v___x_1114_, 2);
lean_dec(v_a_1111_);
lean_dec_ref(v_type_1099_);
v_a_1231_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1117_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1117_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v_type_1099_);
v_a_1239_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1110_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1110_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
v___jp_1107_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___boxed(lean_object* v_type_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0(lean_object* v___x_1256_, lean_object* v_s_1257_){
_start:
{
lean_object* v_exp_1258_; lean_object* v_rings_1259_; lean_object* v_semirings_1260_; lean_object* v_ncRings_1261_; lean_object* v_ncSemirings_1262_; lean_object* v_typeClassify_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_exp_1258_ = lean_ctor_get(v_s_1257_, 0);
v_rings_1259_ = lean_ctor_get(v_s_1257_, 1);
v_semirings_1260_ = lean_ctor_get(v_s_1257_, 2);
v_ncRings_1261_ = lean_ctor_get(v_s_1257_, 3);
v_ncSemirings_1262_ = lean_ctor_get(v_s_1257_, 4);
v_typeClassify_1263_ = lean_ctor_get(v_s_1257_, 5);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_s_1257_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v_s_1257_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_typeClassify_1263_);
lean_inc(v_ncSemirings_1262_);
lean_inc(v_ncRings_1261_);
lean_inc(v_semirings_1260_);
lean_inc(v_rings_1259_);
lean_inc(v_exp_1258_);
lean_dec(v_s_1257_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_array_push(v_ncSemirings_1262_, v___x_1256_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 4, v___x_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_exp_1258_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_rings_1259_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_semirings_1260_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_ncRings_1261_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1270_, 5, v_typeClassify_1263_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(lean_object* v_type_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1284_; 
lean_inc_ref(v_type_1277_);
v___x_1284_ = l_Lean_Meta_getDecLevel(v_type_1277_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc_n(v_a_1285_, 2);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1));
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1288_, 0, v_a_1285_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = l_Lean_mkConst(v___x_1286_, v___x_1288_);
lean_inc_ref(v_type_1277_);
v___x_1290_ = l_Lean_Expr_app___override(v___x_1289_, v_type_1277_);
v___x_1291_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1290_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1341_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1341_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1341_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
if (lean_obj_tag(v_a_1292_) == 1)
{
lean_object* v_val_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1336_; 
lean_del_object(v___x_1294_);
v_val_1296_ = lean_ctor_get(v_a_1292_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_a_1292_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1298_ = v_a_1292_;
v_isShared_1299_ = v_isSharedCheck_1336_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_val_1296_);
lean_dec(v_a_1292_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1336_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1278_, v_a_1281_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v_ncSemirings_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v_ncSemirings_1302_ = lean_ctor_get(v_a_1301_, 4);
lean_inc_ref(v_ncSemirings_1302_);
lean_dec(v_a_1301_);
v___x_1303_ = lean_array_get_size(v_ncSemirings_1302_);
lean_dec_ref(v_ncSemirings_1302_);
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set(v___x_1305_, 1, v_type_1277_);
lean_ctor_set(v___x_1305_, 2, v_a_1285_);
lean_ctor_set(v___x_1305_, 3, v_val_1296_);
lean_ctor_set(v___x_1305_, 4, v___x_1304_);
lean_ctor_set(v___x_1305_, 5, v___x_1304_);
lean_ctor_set(v___x_1305_, 6, v___x_1304_);
lean_ctor_set(v___x_1305_, 7, v___x_1304_);
v___f_1306_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1306_, 0, v___x_1305_);
v___x_1307_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1308_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1307_, v___f_1306_, v_a_1278_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1318_; 
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v___x_1308_, 0);
lean_dec(v_unused_1319_);
v___x_1310_ = v___x_1308_;
v_isShared_1311_ = v_isSharedCheck_1318_;
goto v_resetjp_1309_;
}
else
{
lean_dec(v___x_1308_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1318_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1303_);
v___x_1313_ = v___x_1298_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1303_);
v___x_1313_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1315_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1313_);
v___x_1315_ = v___x_1310_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_del_object(v___x_1298_);
v_a_1320_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1308_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1308_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_del_object(v___x_1298_);
lean_dec(v_val_1296_);
lean_dec(v_a_1285_);
lean_dec_ref(v_type_1277_);
v_a_1328_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1300_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1300_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
lean_dec(v_a_1292_);
lean_dec(v_a_1285_);
lean_dec_ref(v_type_1277_);
v___x_1337_ = lean_box(0);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1337_);
v___x_1339_ = v___x_1294_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_a_1285_);
lean_dec_ref(v_type_1277_);
v_a_1342_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1291_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1291_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v_type_1277_);
v_a_1350_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1284_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1284_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___boxed(lean_object* v_type_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(lean_object* v_type_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_1366_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(lean_object* v_type_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(v_type_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(lean_object* v_type_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1392_; 
lean_inc_ref(v_type_1384_);
v___x_1392_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1487_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1487_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1487_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
if (lean_obj_tag(v_a_1393_) == 1)
{
lean_object* v_val_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v_type_1384_);
v_val_1397_ = lean_ctor_get(v_a_1393_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_a_1393_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1399_ = v_a_1393_;
v_isShared_1400_ = v_isSharedCheck_1407_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_val_1397_);
lean_dec(v_a_1393_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1407_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 0);
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_val_1397_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1402_);
v___x_1404_ = v___x_1395_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v___x_1408_; 
lean_del_object(v___x_1395_);
lean_dec(v_a_1393_);
lean_inc_ref(v_type_1384_);
v___x_1408_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1478_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1478_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1478_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
if (lean_obj_tag(v_a_1409_) == 1)
{
lean_object* v_val_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v_type_1384_);
v_val_1413_ = lean_ctor_get(v_a_1409_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_a_1409_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1415_ = v_a_1409_;
v_isShared_1416_ = v_isSharedCheck_1423_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_val_1413_);
lean_dec(v_a_1409_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1423_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_val_1413_);
v___x_1418_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1418_);
v___x_1420_ = v___x_1411_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
else
{
lean_object* v___x_1424_; 
lean_del_object(v___x_1411_);
lean_dec(v_a_1409_);
lean_inc_ref(v_type_1384_);
v___x_1424_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1469_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1469_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1469_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
if (lean_obj_tag(v_a_1425_) == 1)
{
lean_object* v_val_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1439_; 
lean_dec_ref(v_type_1384_);
v_val_1429_ = lean_ctor_get(v_a_1425_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_a_1425_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1431_ = v_a_1425_;
v_isShared_1432_ = v_isSharedCheck_1439_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_val_1429_);
lean_dec(v_a_1425_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1439_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 2);
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_val_1429_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1434_);
v___x_1436_ = v___x_1427_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v___x_1440_; 
lean_del_object(v___x_1427_);
lean_dec(v_a_1425_);
v___x_1440_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_1384_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1460_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1460_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1460_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
if (lean_obj_tag(v_a_1441_) == 1)
{
lean_object* v_val_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1455_; 
v_val_1445_ = lean_ctor_get(v_a_1441_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_a_1441_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1447_ = v_a_1441_;
v_isShared_1448_ = v_isSharedCheck_1455_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_val_1445_);
lean_dec(v_a_1441_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1455_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 3);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_val_1445_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1450_);
v___x_1452_ = v___x_1443_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_dec(v_a_1441_);
v___x_1456_ = lean_box(4);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1456_);
v___x_1458_ = v___x_1443_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1461_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1440_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1440_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_type_1384_);
v_a_1470_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1424_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1424_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_type_1384_);
v_a_1479_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1408_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1408_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v_type_1384_);
v_a_1488_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1392_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1392_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go___boxed(lean_object* v_type_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(lean_object* v_type_1505_, lean_object* v_a_1506_, lean_object* v_s_1507_){
_start:
{
lean_object* v_exp_1508_; lean_object* v_rings_1509_; lean_object* v_semirings_1510_; lean_object* v_ncRings_1511_; lean_object* v_ncSemirings_1512_; lean_object* v_typeClassify_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1521_; 
v_exp_1508_ = lean_ctor_get(v_s_1507_, 0);
v_rings_1509_ = lean_ctor_get(v_s_1507_, 1);
v_semirings_1510_ = lean_ctor_get(v_s_1507_, 2);
v_ncRings_1511_ = lean_ctor_get(v_s_1507_, 3);
v_ncSemirings_1512_ = lean_ctor_get(v_s_1507_, 4);
v_typeClassify_1513_ = lean_ctor_get(v_s_1507_, 5);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_s_1507_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1515_ = v_s_1507_;
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_typeClassify_1513_);
lean_inc(v_ncSemirings_1512_);
lean_inc(v_ncRings_1511_);
lean_inc(v_semirings_1510_);
lean_inc(v_rings_1509_);
lean_inc(v_exp_1508_);
lean_dec(v_s_1507_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_1513_, v_type_1505_, v_a_1506_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 5, v___x_1517_);
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_exp_1508_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_rings_1509_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_semirings_1510_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_ncRings_1511_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v_ncSemirings_1512_);
lean_ctor_set(v_reuseFailAlloc_1520_, 5, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f(lean_object* v_type_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1524_, v_a_1527_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1562_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1533_ = v___x_1530_;
v_isShared_1534_ = v_isSharedCheck_1562_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1562_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_typeClassify_1535_; lean_object* v___x_1536_; 
v_typeClassify_1535_ = lean_ctor_get(v_a_1531_, 5);
lean_inc_ref(v_typeClassify_1535_);
lean_dec(v_a_1531_);
v___x_1536_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_1535_, v_type_1522_);
lean_dec_ref(v_typeClassify_1535_);
if (lean_obj_tag(v___x_1536_) == 1)
{
lean_object* v_val_1537_; lean_object* v___x_1539_; 
lean_dec_ref(v_type_1522_);
v_val_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v___x_1536_, 1);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v_val_1537_);
v___x_1539_ = v___x_1533_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_val_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
else
{
lean_object* v___x_1541_; 
lean_dec(v___x_1536_);
lean_del_object(v___x_1533_);
lean_inc_ref(v_type_1522_);
v___x_1541_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___f_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc_n(v_a_1542_, 2);
lean_dec_ref_known(v___x_1541_, 1);
v___f_1543_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_classify_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1543_, 0, v_type_1522_);
lean_closure_set(v___f_1543_, 1, v_a_1542_);
v___x_1544_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1545_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1544_, v___f_1543_, v_a_1524_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; 
v_unused_1553_ = lean_ctor_get(v___x_1545_, 0);
lean_dec(v_unused_1553_);
v___x_1547_ = v___x_1545_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_dec(v___x_1545_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v_a_1542_);
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1542_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v_a_1542_);
v_a_1554_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1545_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1545_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_dec_ref(v_type_1522_);
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v_type_1522_);
v_a_1563_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1530_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1530_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___boxed(lean_object* v_type_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Meta_Sym_Arith_classify_x3f(v_type_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
return v_res_1579_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Canon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Canon(uint8_t builtin);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Classify(builtin);
}
#ifdef __cplusplus
}
#endif
