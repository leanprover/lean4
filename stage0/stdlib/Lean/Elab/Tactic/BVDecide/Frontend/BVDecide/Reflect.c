// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.Reflect
// Imports: public import Std.Data.HashMap public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Lean.Meta.AppBuilder public import Lean.Data.RArray
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVBinOp"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 193, 54, 191, 172, 208, 119)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(137, 33, 141, 132, 156, 154, 79, 232)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(68, 221, 44, 95, 169, 9, 73, 176)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(236, 85, 182, 141, 252, 28, 21, 198)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__15;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(66, 46, 226, 27, 15, 162, 209, 81)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__18;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "udiv"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(97, 106, 189, 172, 252, 249, 116, 143)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__21;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "umod"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(185, 164, 216, 8, 44, 82, 23, 11)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVUnOp"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 170, 248, 163, 146, 14, 228, 74)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rotateLeft"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 116, 55, 155, 243, 43, 27, 136)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rotateRight"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(112, 197, 123, 204, 93, 250, 252, 249)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "arithShiftRightConst"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(88, 95, 189, 240, 90, 71, 117, 208)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reverse"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(84, 226, 239, 81, 45, 17, 252, 180)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__15;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "clz"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(221, 66, 219, 130, 52, 97, 84, 10)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__18;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cpop"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(214, 119, 73, 246, 51, 241, 221, 59)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVExpr"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 7, 174, 153, 9, 234, 93, 144)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(213, 213, 79, 77, 131, 135, 136, 165)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__8_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extract"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(13, 22, 63, 119, 146, 191, 248, 8)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(47, 182, 211, 92, 78, 225, 70, 26)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__16;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "un"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__17_value),LEAN_SCALAR_PTR_LITERAL(42, 186, 200, 92, 180, 128, 216, 181)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__19;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__20_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__22_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__21_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__22_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__23;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__24;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__25;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__26_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__27_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__28;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "append"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__29_value),LEAN_SCALAR_PTR_LITERAL(148, 222, 207, 10, 98, 174, 247, 204)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__31;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "replicate"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__32 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__32_value),LEAN_SCALAR_PTR_LITERAL(105, 148, 101, 98, 245, 160, 38, 159)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__34;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "shiftLeft"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__35 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__35_value),LEAN_SCALAR_PTR_LITERAL(197, 209, 242, 75, 214, 61, 180, 95)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__37;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "shiftRight"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__38 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__38_value),LEAN_SCALAR_PTR_LITERAL(71, 199, 243, 56, 253, 18, 242, 226)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__40;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "arithShiftRight"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__41 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__41_value),LEAN_SCALAR_PTR_LITERAL(103, 53, 88, 127, 221, 158, 175, 136)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__43;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "BVBinPred"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 174, 16, 156, 11, 3, 67, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(110, 124, 151, 202, 173, 235, 72, 127)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ult"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 174, 16, 156, 11, 3, 67, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(64, 63, 119, 185, 54, 210, 178, 92)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 174, 16, 156, 11, 3, 67, 199)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Gate"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 125, 195, 121, 220, 103, 239, 120)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__2;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(64, 67, 164, 147, 7, 85, 189, 57)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(208, 118, 173, 79, 191, 184, 148, 203)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__7;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(37, 170, 13, 59, 155, 6, 165, 62)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVPred"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(36, 213, 64, 10, 224, 53, 8, 130)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getLsbD"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(233, 227, 220, 143, 67, 138, 133, 64)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BoolExpr"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "literal"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(124, 170, 215, 35, 43, 27, 202, 11)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__3;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(244, 184, 12, 163, 38, 128, 83, 107)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__12;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(244, 134, 245, 64, 53, 182, 217, 215)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "gate"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(65, 48, 52, 229, 233, 139, 247, 222)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__17;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(222, 47, 143, 42, 137, 9, 112, 75)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "updateAtomsAssignment should only be called when there is an atom"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PackedBitVec"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(53, 26, 122, 246, 246, 235, 136, 91)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___lam__0, .m_arity = 7, .m_num_fixed = 6, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__0_value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "New atom of width "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", synthetic\? "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.Reflect"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Elab.Tactic.BVDecide.Frontend.M.lookup"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "The same atom occurs with different widths, this is a bug"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyTernaryProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__6(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_box(0);
v___x_13_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__5));
v___x_14_ = l_Lean_mkConst(v___x_13_, v___x_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__9(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_box(0);
v___x_23_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__8));
v___x_24_ = l_Lean_mkConst(v___x_23_, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__12(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_box(0);
v___x_33_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__11));
v___x_34_ = l_Lean_mkConst(v___x_33_, v___x_32_);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__15(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = lean_box(0);
v___x_43_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__14));
v___x_44_ = l_Lean_mkConst(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__18(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_box(0);
v___x_53_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__17));
v___x_54_ = l_Lean_mkConst(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__21(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_box(0);
v___x_63_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__20));
v___x_64_ = l_Lean_mkConst(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__24(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_box(0);
v___x_73_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__23));
v___x_74_ = l_Lean_mkConst(v___x_73_, v___x_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0(uint8_t v_x_75_){
_start:
{
switch(v_x_75_)
{
case 0:
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__6);
return v___x_76_;
}
case 1:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__9);
return v___x_77_;
}
case 2:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__12);
return v___x_78_;
}
case 3:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__15);
return v___x_79_;
}
case 4:
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__18, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__18);
return v___x_80_;
}
case 5:
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__21, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__21);
return v___x_81_;
}
default: 
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__24, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__24_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__24);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___boxed(lean_object* v_x_83_){
_start:
{
uint8_t v_x_boxed_84_; lean_object* v_res_85_; 
v_x_boxed_84_ = lean_unbox(v_x_83_);
v_res_85_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0(v_x_boxed_84_);
return v_res_85_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__2(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_box(0);
v___x_93_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__1));
v___x_94_ = l_Lean_mkConst(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__3(void){
_start:
{
lean_object* v___x_95_; lean_object* v___f_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__2);
v___f_96_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__0));
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___f_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___closed__3);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__3(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_box(0);
v___x_108_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__2));
v___x_109_ = l_Lean_mkConst(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__6(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_box(0);
v___x_118_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__5));
v___x_119_ = l_Lean_mkConst(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__9(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_box(0);
v___x_128_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__8));
v___x_129_ = l_Lean_mkConst(v___x_128_, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__12(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_box(0);
v___x_138_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__11));
v___x_139_ = l_Lean_mkConst(v___x_138_, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__15(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__14));
v___x_149_ = l_Lean_mkConst(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__18(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_box(0);
v___x_158_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__17));
v___x_159_ = l_Lean_mkConst(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__21(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_box(0);
v___x_168_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__20));
v___x_169_ = l_Lean_mkConst(v___x_168_, v___x_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0(lean_object* v_x_170_){
_start:
{
switch(lean_obj_tag(v_x_170_))
{
case 0:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__3);
return v___x_171_;
}
case 1:
{
lean_object* v_n_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_n_172_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_n_172_);
lean_dec_ref(v_x_170_);
v___x_173_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__6);
v___x_174_ = l_Lean_mkNatLit(v_n_172_);
v___x_175_ = l_Lean_Expr_app___override(v___x_173_, v___x_174_);
return v___x_175_;
}
case 2:
{
lean_object* v_n_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_n_176_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_n_176_);
lean_dec_ref(v_x_170_);
v___x_177_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__9);
v___x_178_ = l_Lean_mkNatLit(v_n_176_);
v___x_179_ = l_Lean_Expr_app___override(v___x_177_, v___x_178_);
return v___x_179_;
}
case 3:
{
lean_object* v_n_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_n_180_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_n_180_);
lean_dec_ref(v_x_170_);
v___x_181_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__12);
v___x_182_ = l_Lean_mkNatLit(v_n_180_);
v___x_183_ = l_Lean_Expr_app___override(v___x_181_, v___x_182_);
return v___x_183_;
}
case 4:
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__15);
return v___x_184_;
}
case 5:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__18, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__18);
return v___x_185_;
}
default: 
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__21, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__21);
return v___x_186_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__2(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_box(0);
v___x_194_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__1));
v___x_195_ = l_Lean_mkConst(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__3(void){
_start:
{
lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v___x_196_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__2);
v___f_197_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__0));
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___f_197_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___closed__3);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__3(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_box(0);
v___x_209_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__2));
v___x_210_ = l_Lean_mkConst(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__6(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_box(0);
v___x_219_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__5));
v___x_220_ = l_Lean_mkConst(v___x_219_, v___x_218_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__10(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_box(0);
v___x_227_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__9));
v___x_228_ = l_Lean_Expr_const___override(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__13(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_box(0);
v___x_237_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__12));
v___x_238_ = l_Lean_mkConst(v___x_237_, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__16(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_box(0);
v___x_247_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__15));
v___x_248_ = l_Lean_mkConst(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__19(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_box(0);
v___x_257_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__18));
v___x_258_ = l_Lean_mkConst(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__23(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = l_Lean_Level_ofNat(v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__24(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_box(0);
v___x_267_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__23, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__23_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__23);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__25(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__24, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__24_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__24);
v___x_270_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__22));
v___x_271_ = l_Lean_mkConst(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__28(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_box(0);
v___x_276_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__27));
v___x_277_ = l_Lean_mkConst(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__31(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_box(0);
v___x_286_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__30));
v___x_287_ = l_Lean_mkConst(v___x_286_, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__34(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_box(0);
v___x_296_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__33));
v___x_297_ = l_Lean_mkConst(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__37(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_box(0);
v___x_306_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__36));
v___x_307_ = l_Lean_mkConst(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__40(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_box(0);
v___x_316_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__39));
v___x_317_ = l_Lean_mkConst(v___x_316_, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__43(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_box(0);
v___x_326_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__42));
v___x_327_ = l_Lean_mkConst(v___x_326_, v___x_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(lean_object* v_w_328_, lean_object* v_a_329_){
_start:
{
switch(lean_obj_tag(v_a_329_))
{
case 0:
{
lean_object* v_idx_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_idx_330_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_idx_330_);
lean_dec_ref(v_a_329_);
v___x_331_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__3);
v___x_332_ = l_Lean_mkNatLit(v_w_328_);
v___x_333_ = l_Lean_mkNatLit(v_idx_330_);
v___x_334_ = l_Lean_mkAppB(v___x_331_, v___x_332_, v___x_333_);
return v___x_334_;
}
case 1:
{
lean_object* v_val_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_val_335_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_val_335_);
lean_dec_ref(v_a_329_);
v___x_336_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__6);
v___x_337_ = l_Lean_mkNatLit(v_w_328_);
v___x_338_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__10);
v___x_339_ = l_Lean_mkNatLit(v_val_335_);
lean_inc_ref(v___x_337_);
v___x_340_ = l_Lean_mkAppB(v___x_338_, v___x_337_, v___x_339_);
v___x_341_ = l_Lean_mkAppB(v___x_336_, v___x_337_, v___x_340_);
return v___x_341_;
}
case 2:
{
lean_object* v_w_342_; lean_object* v_start_343_; lean_object* v_expr_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_w_342_ = lean_ctor_get(v_a_329_, 0);
lean_inc_n(v_w_342_, 2);
v_start_343_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_start_343_);
v_expr_344_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_expr_344_);
lean_dec_ref(v_a_329_);
v___x_345_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__13);
v___x_346_ = l_Lean_mkNatLit(v_w_342_);
v___x_347_ = l_Lean_mkNatLit(v_start_343_);
v___x_348_ = l_Lean_mkNatLit(v_w_328_);
v___x_349_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_342_, v_expr_344_);
v___x_350_ = l_Lean_mkApp4(v___x_345_, v___x_346_, v___x_347_, v___x_348_, v___x_349_);
return v___x_350_;
}
case 3:
{
lean_object* v_lhs_351_; uint8_t v_op_352_; lean_object* v_rhs_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___y_358_; 
v_lhs_351_ = lean_ctor_get(v_a_329_, 1);
lean_inc_ref(v_lhs_351_);
v_op_352_ = lean_ctor_get_uint8(v_a_329_, sizeof(void*)*3 + 8);
v_rhs_353_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_rhs_353_);
lean_dec_ref(v_a_329_);
v___x_354_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__16, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__16_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__16);
lean_inc_n(v_w_328_, 2);
v___x_355_ = l_Lean_mkNatLit(v_w_328_);
v___x_356_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_328_, v_lhs_351_);
switch(v_op_352_)
{
case 0:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__6);
v___y_358_ = v___x_361_;
goto v___jp_357_;
}
case 1:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__9);
v___y_358_ = v___x_362_;
goto v___jp_357_;
}
case 2:
{
lean_object* v___x_363_; 
v___x_363_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__12);
v___y_358_ = v___x_363_;
goto v___jp_357_;
}
case 3:
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__15);
v___y_358_ = v___x_364_;
goto v___jp_357_;
}
case 4:
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__18, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__18);
v___y_358_ = v___x_365_;
goto v___jp_357_;
}
case 5:
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__21, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__21);
v___y_358_ = v___x_366_;
goto v___jp_357_;
}
default: 
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__24, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__24_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__24);
v___y_358_ = v___x_367_;
goto v___jp_357_;
}
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_328_, v_rhs_353_);
lean_inc_ref(v___y_358_);
v___x_360_ = l_Lean_mkApp4(v___x_354_, v___x_355_, v___x_356_, v___y_358_, v___x_359_);
return v___x_360_;
}
}
case 4:
{
lean_object* v_op_368_; lean_object* v_operand_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___y_373_; 
v_op_368_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_op_368_);
v_operand_369_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_operand_369_);
lean_dec_ref(v_a_329_);
v___x_370_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__19, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__19_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__19);
lean_inc(v_w_328_);
v___x_371_ = l_Lean_mkNatLit(v_w_328_);
switch(lean_obj_tag(v_op_368_))
{
case 0:
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__3);
v___y_373_ = v___x_376_;
goto v___jp_372_;
}
case 1:
{
lean_object* v_n_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_n_377_ = lean_ctor_get(v_op_368_, 0);
lean_inc(v_n_377_);
lean_dec_ref(v_op_368_);
v___x_378_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__6);
v___x_379_ = l_Lean_mkNatLit(v_n_377_);
v___x_380_ = l_Lean_Expr_app___override(v___x_378_, v___x_379_);
v___y_373_ = v___x_380_;
goto v___jp_372_;
}
case 2:
{
lean_object* v_n_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_n_381_ = lean_ctor_get(v_op_368_, 0);
lean_inc(v_n_381_);
lean_dec_ref(v_op_368_);
v___x_382_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__9);
v___x_383_ = l_Lean_mkNatLit(v_n_381_);
v___x_384_ = l_Lean_Expr_app___override(v___x_382_, v___x_383_);
v___y_373_ = v___x_384_;
goto v___jp_372_;
}
case 3:
{
lean_object* v_n_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_n_385_ = lean_ctor_get(v_op_368_, 0);
lean_inc(v_n_385_);
lean_dec_ref(v_op_368_);
v___x_386_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__12);
v___x_387_ = l_Lean_mkNatLit(v_n_385_);
v___x_388_ = l_Lean_Expr_app___override(v___x_386_, v___x_387_);
v___y_373_ = v___x_388_;
goto v___jp_372_;
}
case 4:
{
lean_object* v___x_389_; 
v___x_389_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__15);
v___y_373_ = v___x_389_;
goto v___jp_372_;
}
case 5:
{
lean_object* v___x_390_; 
v___x_390_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__18, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__18);
v___y_373_ = v___x_390_;
goto v___jp_372_;
}
default: 
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__21, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp___lam__0___closed__21);
v___y_373_ = v___x_391_;
goto v___jp_372_;
}
}
v___jp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_328_, v_operand_369_);
v___x_375_ = l_Lean_mkApp3(v___x_370_, v___x_371_, v___y_373_, v___x_374_);
return v___x_375_;
}
}
case 5:
{
lean_object* v_l_392_; lean_object* v_r_393_; lean_object* v_lhs_394_; lean_object* v_rhs_395_; lean_object* v_wExpr_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_proof_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_l_392_ = lean_ctor_get(v_a_329_, 0);
lean_inc_n(v_l_392_, 2);
v_r_393_ = lean_ctor_get(v_a_329_, 1);
lean_inc_n(v_r_393_, 2);
v_lhs_394_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_lhs_394_);
v_rhs_395_ = lean_ctor_get(v_a_329_, 4);
lean_inc_ref(v_rhs_395_);
lean_dec_ref(v_a_329_);
v_wExpr_396_ = l_Lean_mkNatLit(v_w_328_);
v___x_397_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__25);
v___x_398_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__28, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__28_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__28);
lean_inc_ref(v_wExpr_396_);
v_proof_399_ = l_Lean_mkAppB(v___x_397_, v___x_398_, v_wExpr_396_);
v___x_400_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__31, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__31_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__31);
v___x_401_ = l_Lean_mkNatLit(v_l_392_);
v___x_402_ = l_Lean_mkNatLit(v_r_393_);
v___x_403_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_l_392_, v_lhs_394_);
v___x_404_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_r_393_, v_rhs_395_);
v___x_405_ = l_Lean_mkApp6(v___x_400_, v___x_401_, v___x_402_, v_wExpr_396_, v___x_403_, v___x_404_, v_proof_399_);
return v___x_405_;
}
case 6:
{
lean_object* v_w_406_; lean_object* v_n_407_; lean_object* v_expr_408_; lean_object* v_newWExpr_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_proof_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_w_406_ = lean_ctor_get(v_a_329_, 0);
lean_inc_n(v_w_406_, 2);
v_n_407_ = lean_ctor_get(v_a_329_, 2);
lean_inc(v_n_407_);
v_expr_408_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_expr_408_);
lean_dec_ref(v_a_329_);
v_newWExpr_409_ = l_Lean_mkNatLit(v_w_328_);
v___x_410_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__25);
v___x_411_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__28, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__28_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__28);
lean_inc_ref(v_newWExpr_409_);
v_proof_412_ = l_Lean_mkAppB(v___x_410_, v___x_411_, v_newWExpr_409_);
v___x_413_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__34);
v___x_414_ = l_Lean_mkNatLit(v_w_406_);
v___x_415_ = l_Lean_mkNatLit(v_n_407_);
v___x_416_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_406_, v_expr_408_);
v___x_417_ = l_Lean_mkApp5(v___x_413_, v___x_414_, v_newWExpr_409_, v___x_415_, v___x_416_, v_proof_412_);
return v___x_417_;
}
case 7:
{
lean_object* v_n_418_; lean_object* v_lhs_419_; lean_object* v_rhs_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_n_418_ = lean_ctor_get(v_a_329_, 1);
lean_inc_n(v_n_418_, 2);
v_lhs_419_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_lhs_419_);
v_rhs_420_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_rhs_420_);
lean_dec_ref(v_a_329_);
v___x_421_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__37, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__37_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__37);
lean_inc(v_w_328_);
v___x_422_ = l_Lean_mkNatLit(v_w_328_);
v___x_423_ = l_Lean_mkNatLit(v_n_418_);
v___x_424_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_328_, v_lhs_419_);
v___x_425_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_n_418_, v_rhs_420_);
v___x_426_ = l_Lean_mkApp4(v___x_421_, v___x_422_, v___x_423_, v___x_424_, v___x_425_);
return v___x_426_;
}
case 8:
{
lean_object* v_n_427_; lean_object* v_lhs_428_; lean_object* v_rhs_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_n_427_ = lean_ctor_get(v_a_329_, 1);
lean_inc_n(v_n_427_, 2);
v_lhs_428_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_lhs_428_);
v_rhs_429_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_rhs_429_);
lean_dec_ref(v_a_329_);
v___x_430_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__40, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__40_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__40);
lean_inc(v_w_328_);
v___x_431_ = l_Lean_mkNatLit(v_w_328_);
v___x_432_ = l_Lean_mkNatLit(v_n_427_);
v___x_433_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_328_, v_lhs_428_);
v___x_434_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_n_427_, v_rhs_429_);
v___x_435_ = l_Lean_mkApp4(v___x_430_, v___x_431_, v___x_432_, v___x_433_, v___x_434_);
return v___x_435_;
}
default: 
{
lean_object* v_n_436_; lean_object* v_lhs_437_; lean_object* v_rhs_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_n_436_ = lean_ctor_get(v_a_329_, 1);
lean_inc_n(v_n_436_, 2);
v_lhs_437_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_lhs_437_);
v_rhs_438_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_rhs_438_);
lean_dec_ref(v_a_329_);
v___x_439_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__43, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__43_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__43);
lean_inc(v_w_328_);
v___x_440_ = l_Lean_mkNatLit(v_w_328_);
v___x_441_ = l_Lean_mkNatLit(v_n_436_);
v___x_442_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_328_, v_lhs_437_);
v___x_443_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_n_436_, v_rhs_438_);
v___x_444_ = l_Lean_mkApp4(v___x_439_, v___x_440_, v___x_441_, v___x_442_, v___x_443_);
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___lam__0(lean_object* v_w_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_445_, v_x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__1(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_box(0);
v___x_454_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__0));
v___x_455_ = l_Lean_mkConst(v___x_454_, v___x_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr(lean_object* v_w_456_){
_start:
{
lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc(v_w_456_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___lam__0), 2, 1);
lean_closure_set(v___f_457_, 0, v_w_456_);
v___x_458_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr___closed__1);
v___x_459_ = l_Lean_mkNatLit(v_w_456_);
v___x_460_ = l_Lean_Expr_app___override(v___x_458_, v___x_459_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___f_457_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__3(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
v___x_471_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__2));
v___x_472_ = l_Lean_mkConst(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__6(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_box(0);
v___x_481_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__5));
v___x_482_ = l_Lean_mkConst(v___x_481_, v___x_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0(uint8_t v_x_483_){
_start:
{
if (v_x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__3);
return v___x_484_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__6);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___boxed(lean_object* v_x_486_){
_start:
{
uint8_t v_x_boxed_487_; lean_object* v_res_488_; 
v_x_boxed_487_ = lean_unbox(v_x_486_);
v_res_488_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0(v_x_boxed_487_);
return v_res_488_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__2(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_box(0);
v___x_496_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__1));
v___x_497_ = l_Lean_mkConst(v___x_496_, v___x_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__3(void){
_start:
{
lean_object* v___x_498_; lean_object* v___f_499_; lean_object* v___x_500_; 
v___x_498_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__2);
v___f_499_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__0));
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___f_499_);
lean_ctor_set(v___x_500_, 1, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred(void){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___closed__3);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__2(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_box(0);
v___x_510_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__1));
v___x_511_ = l_Lean_mkConst(v___x_510_, v___x_509_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__4(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_box(0);
v___x_519_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__3));
v___x_520_ = l_Lean_mkConst(v___x_519_, v___x_518_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__7(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_box(0);
v___x_529_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__6));
v___x_530_ = l_Lean_mkConst(v___x_529_, v___x_528_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__9(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_box(0);
v___x_538_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__8));
v___x_539_ = l_Lean_mkConst(v___x_538_, v___x_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0(uint8_t v_x_540_){
_start:
{
switch(v_x_540_)
{
case 0:
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__2);
return v___x_541_;
}
case 1:
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__4);
return v___x_542_;
}
case 2:
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__7);
return v___x_543_;
}
default: 
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__9);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___boxed(lean_object* v_x_545_){
_start:
{
uint8_t v_x_boxed_546_; lean_object* v_res_547_; 
v_x_boxed_546_ = lean_unbox(v_x_545_);
v_res_547_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0(v_x_boxed_546_);
return v_res_547_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__2(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_box(0);
v___x_555_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__1));
v___x_556_ = l_Lean_mkConst(v___x_555_, v___x_554_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__3(void){
_start:
{
lean_object* v___x_557_; lean_object* v___f_558_; lean_object* v___x_559_; 
v___x_557_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__2);
v___f_558_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__0));
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___f_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate(void){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___closed__3);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__2(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = lean_box(0);
v___x_569_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__1));
v___x_570_ = l_Lean_mkConst(v___x_569_, v___x_568_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__5(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_box(0);
v___x_579_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__4));
v___x_580_ = l_Lean_mkConst(v___x_579_, v___x_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go(lean_object* v_a_581_){
_start:
{
if (lean_obj_tag(v_a_581_) == 0)
{
lean_object* v_w_582_; lean_object* v_lhs_583_; uint8_t v_op_584_; lean_object* v_rhs_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___y_590_; 
v_w_582_ = lean_ctor_get(v_a_581_, 0);
lean_inc_n(v_w_582_, 3);
v_lhs_583_ = lean_ctor_get(v_a_581_, 1);
lean_inc_ref(v_lhs_583_);
v_op_584_ = lean_ctor_get_uint8(v_a_581_, sizeof(void*)*3);
v_rhs_585_ = lean_ctor_get(v_a_581_, 2);
lean_inc_ref(v_rhs_585_);
lean_dec_ref(v_a_581_);
v___x_586_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__2);
v___x_587_ = l_Lean_mkNatLit(v_w_582_);
v___x_588_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_582_, v_lhs_583_);
if (v_op_584_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__3);
v___y_590_ = v___x_593_;
goto v___jp_589_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred___lam__0___closed__6);
v___y_590_ = v___x_594_;
goto v___jp_589_;
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_582_, v_rhs_585_);
lean_inc_ref(v___y_590_);
v___x_592_ = l_Lean_mkApp4(v___x_586_, v___x_587_, v___x_588_, v___y_590_, v___x_591_);
return v___x_592_;
}
}
else
{
lean_object* v_w_595_; lean_object* v_expr_596_; lean_object* v_idx_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_w_595_ = lean_ctor_get(v_a_581_, 0);
lean_inc_n(v_w_595_, 2);
v_expr_596_ = lean_ctor_get(v_a_581_, 1);
lean_inc_ref(v_expr_596_);
v_idx_597_ = lean_ctor_get(v_a_581_, 2);
lean_inc(v_idx_597_);
lean_dec_ref(v_a_581_);
v___x_598_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__5);
v___x_599_ = l_Lean_mkNatLit(v_w_595_);
v___x_600_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go(v_w_595_, v_expr_596_);
v___x_601_ = l_Lean_mkNatLit(v_idx_597_);
v___x_602_ = l_Lean_mkApp3(v___x_598_, v___x_599_, v___x_600_, v___x_601_);
return v___x_602_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__2(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_box(0);
v___x_610_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__1));
v___x_611_ = l_Lean_mkConst(v___x_610_, v___x_609_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__3(void){
_start:
{
lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___x_614_; 
v___x_612_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__2);
v___f_613_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__0));
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___f_613_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred___closed__3);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_box(0);
v___x_625_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__2));
v___x_626_ = l_Lean_mkConst(v___x_625_, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__5(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_box(0);
v___x_634_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__4));
v___x_635_ = l_Lean_mkConst(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__9(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_box(0);
v___x_642_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__8));
v___x_643_ = l_Lean_mkConst(v___x_642_, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__12(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_box(0);
v___x_649_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__11));
v___x_650_ = l_Lean_mkConst(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__14(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
v___x_658_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__13));
v___x_659_ = l_Lean_mkConst(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__17(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_box(0);
v___x_668_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__16));
v___x_669_ = l_Lean_mkConst(v___x_668_, v___x_667_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__20(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_box(0);
v___x_678_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__19));
v___x_679_ = l_Lean_mkConst(v___x_678_, v___x_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(lean_object* v_inst_680_, lean_object* v_a_681_){
_start:
{
switch(lean_obj_tag(v_a_681_))
{
case 0:
{
lean_object* v_a_682_; lean_object* v_toExpr_683_; lean_object* v_toTypeExpr_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_a_682_ = lean_ctor_get(v_a_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v_a_681_);
v_toExpr_683_ = lean_ctor_get(v_inst_680_, 0);
lean_inc_ref(v_toExpr_683_);
v_toTypeExpr_684_ = lean_ctor_get(v_inst_680_, 1);
lean_inc_ref(v_toTypeExpr_684_);
lean_dec_ref(v_inst_680_);
v___x_685_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__3);
v___x_686_ = lean_apply_1(v_toExpr_683_, v_a_682_);
v___x_687_ = l_Lean_mkAppB(v___x_685_, v_toTypeExpr_684_, v___x_686_);
return v___x_687_;
}
case 1:
{
uint8_t v_a_688_; lean_object* v_toTypeExpr_689_; lean_object* v___x_690_; 
v_a_688_ = lean_ctor_get_uint8(v_a_681_, 0);
lean_dec_ref(v_a_681_);
v_toTypeExpr_689_ = lean_ctor_get(v_inst_680_, 1);
lean_inc_ref(v_toTypeExpr_689_);
lean_dec_ref(v_inst_680_);
v___x_690_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__5);
if (v_a_688_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__9);
v___x_692_ = l_Lean_mkAppB(v___x_690_, v_toTypeExpr_689_, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__12);
v___x_694_ = l_Lean_mkAppB(v___x_690_, v_toTypeExpr_689_, v___x_693_);
return v___x_694_;
}
}
case 2:
{
lean_object* v_a_695_; lean_object* v_toTypeExpr_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_a_695_ = lean_ctor_get(v_a_681_, 0);
lean_inc_ref(v_a_695_);
lean_dec_ref(v_a_681_);
v_toTypeExpr_696_ = lean_ctor_get(v_inst_680_, 1);
lean_inc_ref(v_toTypeExpr_696_);
v___x_697_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__14, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__14_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__14);
v___x_698_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_695_);
v___x_699_ = l_Lean_mkAppB(v___x_697_, v_toTypeExpr_696_, v___x_698_);
return v___x_699_;
}
case 3:
{
uint8_t v_a_700_; lean_object* v_a_701_; lean_object* v_a_702_; lean_object* v_toTypeExpr_703_; lean_object* v___x_704_; lean_object* v___y_706_; 
v_a_700_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*2);
v_a_701_ = lean_ctor_get(v_a_681_, 0);
lean_inc_ref(v_a_701_);
v_a_702_ = lean_ctor_get(v_a_681_, 1);
lean_inc_ref(v_a_702_);
lean_dec_ref(v_a_681_);
v_toTypeExpr_703_ = lean_ctor_get(v_inst_680_, 1);
lean_inc_ref(v_toTypeExpr_703_);
v___x_704_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__17, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__17_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__17);
switch(v_a_700_)
{
case 0:
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__2);
v___y_706_ = v___x_710_;
goto v___jp_705_;
}
case 1:
{
lean_object* v___x_711_; 
v___x_711_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__4);
v___y_706_ = v___x_711_;
goto v___jp_705_;
}
case 2:
{
lean_object* v___x_712_; 
v___x_712_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__7);
v___y_706_ = v___x_712_;
goto v___jp_705_;
}
default: 
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate___lam__0___closed__9);
v___y_706_ = v___x_713_;
goto v___jp_705_;
}
}
v___jp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_inc_ref(v_inst_680_);
v___x_707_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_701_);
v___x_708_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_702_);
lean_inc_ref(v___y_706_);
v___x_709_ = l_Lean_mkApp4(v___x_704_, v_toTypeExpr_703_, v___y_706_, v___x_707_, v___x_708_);
return v___x_709_;
}
}
default: 
{
lean_object* v_a_714_; lean_object* v_a_715_; lean_object* v_a_716_; lean_object* v_toTypeExpr_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_a_714_ = lean_ctor_get(v_a_681_, 0);
lean_inc_ref(v_a_714_);
v_a_715_ = lean_ctor_get(v_a_681_, 1);
lean_inc_ref(v_a_715_);
v_a_716_ = lean_ctor_get(v_a_681_, 2);
lean_inc_ref(v_a_716_);
lean_dec_ref(v_a_681_);
v_toTypeExpr_717_ = lean_ctor_get(v_inst_680_, 1);
lean_inc_ref(v_toTypeExpr_717_);
v___x_718_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__20, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__20_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__20);
lean_inc_ref_n(v_inst_680_, 2);
v___x_719_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_714_);
v___x_720_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_715_);
v___x_721_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_716_);
v___x_722_ = l_Lean_mkApp4(v___x_718_, v_toTypeExpr_717_, v___x_719_, v___x_720_, v___x_721_);
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go(lean_object* v_00_u03b1_723_, lean_object* v_inst_724_, lean_object* v_a_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(v_inst_724_, v_a_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___lam__0(lean_object* v_inst_727_, lean_object* v_x_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(v_inst_727_, v_x_728_);
return v___x_729_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_box(0);
v___x_736_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__0));
v___x_737_ = l_Lean_mkConst(v___x_736_, v___x_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg(lean_object* v_inst_738_){
_start:
{
lean_object* v_toTypeExpr_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_toTypeExpr_739_ = lean_ctor_get(v_inst_738_, 1);
lean_inc_ref(v_toTypeExpr_739_);
v___f_740_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___lam__0), 2, 1);
lean_closure_set(v___f_740_, 0, v_inst_738_);
v___x_741_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg___closed__1);
v___x_742_ = l_Lean_Expr_app___override(v___x_741_, v_toTypeExpr_739_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___f_740_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr(lean_object* v_00_u03b1_744_, lean_object* v_inst_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr___redArg(v_inst_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(lean_object* v_a_747_, lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v___x_749_; 
v___x_749_ = lean_box(0);
return v___x_749_;
}
else
{
lean_object* v_key_750_; lean_object* v_value_751_; lean_object* v_tail_752_; uint8_t v___x_753_; 
v_key_750_ = lean_ctor_get(v_x_748_, 0);
v_value_751_ = lean_ctor_get(v_x_748_, 1);
v_tail_752_ = lean_ctor_get(v_x_748_, 2);
v___x_753_ = lean_expr_eqv(v_key_750_, v_a_747_);
if (v___x_753_ == 0)
{
v_x_748_ = v_tail_752_;
goto _start;
}
else
{
lean_object* v___x_755_; 
lean_inc(v_value_751_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v_value_751_);
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg___boxed(lean_object* v_a_756_, lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_756_, v_x_757_);
lean_dec(v_x_757_);
lean_dec_ref(v_a_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(lean_object* v_m_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_buckets_761_; lean_object* v___x_762_; uint64_t v___x_763_; uint64_t v___x_764_; uint64_t v___x_765_; uint64_t v_fold_766_; uint64_t v___x_767_; uint64_t v___x_768_; uint64_t v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_buckets_761_ = lean_ctor_get(v_m_759_, 1);
v___x_762_ = lean_array_get_size(v_buckets_761_);
v___x_763_ = l_Lean_Expr_hash(v_a_760_);
v___x_764_ = 32ULL;
v___x_765_ = lean_uint64_shift_right(v___x_763_, v___x_764_);
v_fold_766_ = lean_uint64_xor(v___x_763_, v___x_765_);
v___x_767_ = 16ULL;
v___x_768_ = lean_uint64_shift_right(v_fold_766_, v___x_767_);
v___x_769_ = lean_uint64_xor(v_fold_766_, v___x_768_);
v___x_770_ = lean_uint64_to_usize(v___x_769_);
v___x_771_ = lean_usize_of_nat(v___x_762_);
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_sub(v___x_771_, v___x_772_);
v___x_774_ = lean_usize_land(v___x_770_, v___x_773_);
v___x_775_ = lean_array_uget_borrowed(v_buckets_761_, v___x_774_);
v___x_776_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_760_, v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg___boxed(lean_object* v_m_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_m_777_, v_a_778_);
lean_dec_ref(v_a_778_);
lean_dec_ref(v_m_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(lean_object* v_a_780_, lean_object* v_b_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_dec(v_b_781_);
lean_dec_ref(v_a_780_);
return v_x_782_;
}
else
{
lean_object* v_key_783_; lean_object* v_value_784_; lean_object* v_tail_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_797_; 
v_key_783_ = lean_ctor_get(v_x_782_, 0);
v_value_784_ = lean_ctor_get(v_x_782_, 1);
v_tail_785_ = lean_ctor_get(v_x_782_, 2);
v_isSharedCheck_797_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_797_ == 0)
{
v___x_787_ = v_x_782_;
v_isShared_788_ = v_isSharedCheck_797_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_tail_785_);
lean_inc(v_value_784_);
lean_inc(v_key_783_);
lean_dec(v_x_782_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_797_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
uint8_t v___x_789_; 
v___x_789_ = lean_expr_eqv(v_key_783_, v_a_780_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_780_, v_b_781_, v_tail_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 2, v___x_790_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_key_783_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_value_784_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_object* v___x_795_; 
lean_dec(v_value_784_);
lean_dec(v_key_783_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_b_781_);
lean_ctor_set(v___x_787_, 0, v_a_780_);
v___x_795_ = v___x_787_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_780_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_b_781_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_tail_785_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_799_) == 0)
{
return v_x_798_;
}
else
{
lean_object* v_key_800_; lean_object* v_value_801_; lean_object* v_tail_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_825_; 
v_key_800_ = lean_ctor_get(v_x_799_, 0);
v_value_801_ = lean_ctor_get(v_x_799_, 1);
v_tail_802_ = lean_ctor_get(v_x_799_, 2);
v_isSharedCheck_825_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_825_ == 0)
{
v___x_804_ = v_x_799_;
v_isShared_805_ = v_isSharedCheck_825_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_tail_802_);
lean_inc(v_value_801_);
lean_inc(v_key_800_);
lean_dec(v_x_799_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_825_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; uint64_t v___x_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v_fold_810_; uint64_t v___x_811_; uint64_t v___x_812_; uint64_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_806_ = lean_array_get_size(v_x_798_);
v___x_807_ = l_Lean_Expr_hash(v_key_800_);
v___x_808_ = 32ULL;
v___x_809_ = lean_uint64_shift_right(v___x_807_, v___x_808_);
v_fold_810_ = lean_uint64_xor(v___x_807_, v___x_809_);
v___x_811_ = 16ULL;
v___x_812_ = lean_uint64_shift_right(v_fold_810_, v___x_811_);
v___x_813_ = lean_uint64_xor(v_fold_810_, v___x_812_);
v___x_814_ = lean_uint64_to_usize(v___x_813_);
v___x_815_ = lean_usize_of_nat(v___x_806_);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_sub(v___x_815_, v___x_816_);
v___x_818_ = lean_usize_land(v___x_814_, v___x_817_);
v___x_819_ = lean_array_uget_borrowed(v_x_798_, v___x_818_);
lean_inc(v___x_819_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 2, v___x_819_);
v___x_821_ = v___x_804_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_key_800_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_value_801_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v___x_819_);
v___x_821_ = v_reuseFailAlloc_824_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; 
v___x_822_ = lean_array_uset(v_x_798_, v___x_818_, v___x_821_);
v_x_798_ = v___x_822_;
v_x_799_ = v_tail_802_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(lean_object* v_i_826_, lean_object* v_source_827_, lean_object* v_target_828_){
_start:
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = lean_array_get_size(v_source_827_);
v___x_830_ = lean_nat_dec_lt(v_i_826_, v___x_829_);
if (v___x_830_ == 0)
{
lean_dec_ref(v_source_827_);
lean_dec(v_i_826_);
return v_target_828_;
}
else
{
lean_object* v_es_831_; lean_object* v___x_832_; lean_object* v_source_833_; lean_object* v_target_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_es_831_ = lean_array_fget(v_source_827_, v_i_826_);
v___x_832_ = lean_box(0);
v_source_833_ = lean_array_fset(v_source_827_, v_i_826_, v___x_832_);
v_target_834_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(v_target_828_, v_es_831_);
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_add(v_i_826_, v___x_835_);
lean_dec(v_i_826_);
v_i_826_ = v___x_836_;
v_source_827_ = v_source_833_;
v_target_828_ = v_target_834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(lean_object* v_data_838_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v_nbuckets_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_839_ = lean_array_get_size(v_data_838_);
v___x_840_ = lean_unsigned_to_nat(2u);
v_nbuckets_841_ = lean_nat_mul(v___x_839_, v___x_840_);
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_box(0);
v___x_844_ = lean_mk_array(v_nbuckets_841_, v___x_843_);
v___x_845_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(v___x_842_, v_data_838_, v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(lean_object* v_a_846_, lean_object* v_x_847_){
_start:
{
if (lean_obj_tag(v_x_847_) == 0)
{
uint8_t v___x_848_; 
v___x_848_ = 0;
return v___x_848_;
}
else
{
lean_object* v_key_849_; lean_object* v_tail_850_; uint8_t v___x_851_; 
v_key_849_ = lean_ctor_get(v_x_847_, 0);
v_tail_850_ = lean_ctor_get(v_x_847_, 2);
v___x_851_ = lean_expr_eqv(v_key_849_, v_a_846_);
if (v___x_851_ == 0)
{
v_x_847_ = v_tail_850_;
goto _start;
}
else
{
return v___x_851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg___boxed(lean_object* v_a_853_, lean_object* v_x_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_853_, v_x_854_);
lean_dec(v_x_854_);
lean_dec_ref(v_a_853_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(lean_object* v_m_857_, lean_object* v_a_858_, lean_object* v_b_859_){
_start:
{
lean_object* v_size_860_; lean_object* v_buckets_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_904_; 
v_size_860_ = lean_ctor_get(v_m_857_, 0);
v_buckets_861_ = lean_ctor_get(v_m_857_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_m_857_);
if (v_isSharedCheck_904_ == 0)
{
v___x_863_ = v_m_857_;
v_isShared_864_ = v_isSharedCheck_904_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_buckets_861_);
lean_inc(v_size_860_);
lean_dec(v_m_857_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_904_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; uint64_t v___x_866_; uint64_t v___x_867_; uint64_t v___x_868_; uint64_t v_fold_869_; uint64_t v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; size_t v___x_876_; size_t v___x_877_; lean_object* v_bkt_878_; uint8_t v___x_879_; 
v___x_865_ = lean_array_get_size(v_buckets_861_);
v___x_866_ = l_Lean_Expr_hash(v_a_858_);
v___x_867_ = 32ULL;
v___x_868_ = lean_uint64_shift_right(v___x_866_, v___x_867_);
v_fold_869_ = lean_uint64_xor(v___x_866_, v___x_868_);
v___x_870_ = 16ULL;
v___x_871_ = lean_uint64_shift_right(v_fold_869_, v___x_870_);
v___x_872_ = lean_uint64_xor(v_fold_869_, v___x_871_);
v___x_873_ = lean_uint64_to_usize(v___x_872_);
v___x_874_ = lean_usize_of_nat(v___x_865_);
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_sub(v___x_874_, v___x_875_);
v___x_877_ = lean_usize_land(v___x_873_, v___x_876_);
v_bkt_878_ = lean_array_uget_borrowed(v_buckets_861_, v___x_877_);
v___x_879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_858_, v_bkt_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v_size_x27_881_; lean_object* v___x_882_; lean_object* v_buckets_x27_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_880_ = lean_unsigned_to_nat(1u);
v_size_x27_881_ = lean_nat_add(v_size_860_, v___x_880_);
lean_dec(v_size_860_);
lean_inc(v_bkt_878_);
v___x_882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_882_, 0, v_a_858_);
lean_ctor_set(v___x_882_, 1, v_b_859_);
lean_ctor_set(v___x_882_, 2, v_bkt_878_);
v_buckets_x27_883_ = lean_array_uset(v_buckets_861_, v___x_877_, v___x_882_);
v___x_884_ = lean_unsigned_to_nat(4u);
v___x_885_ = lean_nat_mul(v_size_x27_881_, v___x_884_);
v___x_886_ = lean_unsigned_to_nat(3u);
v___x_887_ = lean_nat_div(v___x_885_, v___x_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_array_get_size(v_buckets_x27_883_);
v___x_889_ = lean_nat_dec_le(v___x_887_, v___x_888_);
lean_dec(v___x_887_);
if (v___x_889_ == 0)
{
lean_object* v_val_890_; lean_object* v___x_892_; 
v_val_890_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(v_buckets_x27_883_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_val_890_);
lean_ctor_set(v___x_863_, 0, v_size_x27_881_);
v___x_892_ = v___x_863_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_size_x27_881_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_val_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
lean_object* v___x_895_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_buckets_x27_883_);
lean_ctor_set(v___x_863_, 0, v_size_x27_881_);
v___x_895_ = v___x_863_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_size_x27_881_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_buckets_x27_883_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v___x_897_; lean_object* v_buckets_x27_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
lean_inc(v_bkt_878_);
v___x_897_ = lean_box(0);
v_buckets_x27_898_ = lean_array_uset(v_buckets_861_, v___x_877_, v___x_897_);
v___x_899_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_858_, v_b_859_, v_bkt_878_);
v___x_900_ = lean_array_uset(v_buckets_x27_898_, v___x_877_, v___x_899_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___x_900_);
v___x_902_ = v___x_863_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_size_860_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(lean_object* v_reified_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; lean_object* v_evalsAtCache_913_; lean_object* v_originalExpr_914_; lean_object* v_evalsAtAtoms_x27_915_; lean_object* v___x_916_; 
v___x_912_ = lean_st_ref_get(v_a_906_);
v_evalsAtCache_913_ = lean_ctor_get(v___x_912_, 2);
lean_inc_ref(v_evalsAtCache_913_);
lean_dec(v___x_912_);
v_originalExpr_914_ = lean_ctor_get(v_reified_905_, 2);
lean_inc_ref(v_originalExpr_914_);
v_evalsAtAtoms_x27_915_ = lean_ctor_get(v_reified_905_, 3);
lean_inc_ref(v_evalsAtAtoms_x27_915_);
lean_dec_ref(v_reified_905_);
v___x_916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_913_, v_originalExpr_914_);
lean_dec_ref(v_evalsAtCache_913_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v___x_917_; 
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc_ref(v_a_907_);
lean_inc(v_a_906_);
v___x_917_ = lean_apply_6(v_evalsAtAtoms_x27_915_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, lean_box(0));
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_938_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_938_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_938_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_938_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v_atoms_923_; lean_object* v_atomsAssignmentCache_924_; lean_object* v_evalsAtCache_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_937_; 
v___x_922_ = lean_st_ref_take(v_a_906_);
v_atoms_923_ = lean_ctor_get(v___x_922_, 0);
v_atomsAssignmentCache_924_ = lean_ctor_get(v___x_922_, 1);
v_evalsAtCache_925_ = lean_ctor_get(v___x_922_, 2);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_937_ == 0)
{
v___x_927_ = v___x_922_;
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_evalsAtCache_925_);
lean_inc(v_atomsAssignmentCache_924_);
lean_inc(v_atoms_923_);
lean_dec(v___x_922_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
lean_inc(v_a_918_);
v___x_929_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_925_, v_originalExpr_914_, v_a_918_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 2, v___x_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_atoms_923_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_atomsAssignmentCache_924_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v___x_929_);
v___x_931_ = v_reuseFailAlloc_936_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_st_ref_set(v_a_906_, v___x_931_);
if (v_isShared_921_ == 0)
{
v___x_934_ = v___x_920_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_918_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_914_);
return v___x_917_;
}
}
else
{
lean_object* v_val_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec_ref(v_evalsAtAtoms_x27_915_);
lean_dec_ref(v_originalExpr_914_);
v_val_939_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_916_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_val_939_);
lean_dec(v___x_916_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 0);
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_val_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms___boxed(lean_object* v_reified_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(v_reified_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0(lean_object* v_00_u03b2_955_, lean_object* v_m_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_m_956_, v_a_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___boxed(lean_object* v_00_u03b2_959_, lean_object* v_m_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0(v_00_u03b2_959_, v_m_960_, v_a_961_);
lean_dec_ref(v_a_961_);
lean_dec_ref(v_m_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1(lean_object* v_00_u03b2_963_, lean_object* v_m_964_, lean_object* v_a_965_, lean_object* v_b_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_m_964_, v_a_965_, v_b_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(lean_object* v_00_u03b2_968_, lean_object* v_a_969_, lean_object* v_x_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_969_, v_x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_972_, lean_object* v_a_973_, lean_object* v_x_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(v_00_u03b2_972_, v_a_973_, v_x_974_);
lean_dec(v_x_974_);
lean_dec_ref(v_a_973_);
return v_res_975_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(lean_object* v_00_u03b2_976_, lean_object* v_a_977_, lean_object* v_x_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_977_, v_x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___boxed(lean_object* v_00_u03b2_980_, lean_object* v_a_981_, lean_object* v_x_982_){
_start:
{
uint8_t v_res_983_; lean_object* v_r_984_; 
v_res_983_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(v_00_u03b2_980_, v_a_981_, v_x_982_);
lean_dec(v_x_982_);
lean_dec_ref(v_a_981_);
v_r_984_ = lean_box(v_res_983_);
return v_r_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3(lean_object* v_00_u03b2_985_, lean_object* v_data_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(v_data_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4(lean_object* v_00_u03b2_988_, lean_object* v_a_989_, lean_object* v_b_990_, lean_object* v_x_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_989_, v_b_990_, v_x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_993_, lean_object* v_i_994_, lean_object* v_source_995_, lean_object* v_target_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(v_i_994_, v_source_995_, v_target_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(v_x_999_, v_x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_evalsAtAtoms(lean_object* v_reified_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v_evalsAtCache_1010_; lean_object* v_originalExpr_1011_; lean_object* v_evalsAtAtoms_x27_1012_; lean_object* v___x_1013_; 
v___x_1009_ = lean_st_ref_get(v_a_1003_);
v_evalsAtCache_1010_ = lean_ctor_get(v___x_1009_, 2);
lean_inc_ref(v_evalsAtCache_1010_);
lean_dec(v___x_1009_);
v_originalExpr_1011_ = lean_ctor_get(v_reified_1002_, 1);
lean_inc_ref(v_originalExpr_1011_);
v_evalsAtAtoms_x27_1012_ = lean_ctor_get(v_reified_1002_, 2);
lean_inc_ref(v_evalsAtAtoms_x27_1012_);
lean_dec_ref(v_reified_1002_);
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_1010_, v_originalExpr_1011_);
lean_dec_ref(v_evalsAtCache_1010_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v___x_1014_; 
lean_inc(v_a_1007_);
lean_inc_ref(v_a_1006_);
lean_inc(v_a_1005_);
lean_inc_ref(v_a_1004_);
lean_inc(v_a_1003_);
v___x_1014_ = lean_apply_6(v_evalsAtAtoms_x27_1012_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, lean_box(0));
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1035_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1035_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1035_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v_atoms_1020_; lean_object* v_atomsAssignmentCache_1021_; lean_object* v_evalsAtCache_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1034_; 
v___x_1019_ = lean_st_ref_take(v_a_1003_);
v_atoms_1020_ = lean_ctor_get(v___x_1019_, 0);
v_atomsAssignmentCache_1021_ = lean_ctor_get(v___x_1019_, 1);
v_evalsAtCache_1022_ = lean_ctor_get(v___x_1019_, 2);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1024_ = v___x_1019_;
v_isShared_1025_ = v_isSharedCheck_1034_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_evalsAtCache_1022_);
lean_inc(v_atomsAssignmentCache_1021_);
lean_inc(v_atoms_1020_);
lean_dec(v___x_1019_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1034_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_inc(v_a_1015_);
v___x_1026_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_1022_, v_originalExpr_1011_, v_a_1015_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 2, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_atoms_1020_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_atomsAssignmentCache_1021_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_st_ref_set(v_a_1003_, v___x_1028_);
if (v_isShared_1018_ == 0)
{
v___x_1031_ = v___x_1017_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1015_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_1011_);
return v___x_1014_;
}
}
else
{
lean_object* v_val_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec_ref(v_evalsAtAtoms_x27_1012_);
lean_dec_ref(v_originalExpr_1011_);
v_val_1036_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1013_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_val_1036_);
lean_dec(v___x_1013_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 0);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_val_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_evalsAtAtoms___boxed(lean_object* v_reified_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_evalsAtAtoms(v_reified_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_evalsAtAtoms(lean_object* v_reified_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v_evalsAtCache_1060_; lean_object* v_originalExpr_1061_; lean_object* v_evalsAtAtoms_x27_1062_; lean_object* v___x_1063_; 
v___x_1059_ = lean_st_ref_get(v_a_1053_);
v_evalsAtCache_1060_ = lean_ctor_get(v___x_1059_, 2);
lean_inc_ref(v_evalsAtCache_1060_);
lean_dec(v___x_1059_);
v_originalExpr_1061_ = lean_ctor_get(v_reified_1052_, 1);
lean_inc_ref(v_originalExpr_1061_);
v_evalsAtAtoms_x27_1062_ = lean_ctor_get(v_reified_1052_, 2);
lean_inc_ref(v_evalsAtAtoms_x27_1062_);
lean_dec_ref(v_reified_1052_);
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_1060_, v_originalExpr_1061_);
lean_dec_ref(v_evalsAtCache_1060_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v___x_1064_; 
lean_inc(v_a_1057_);
lean_inc_ref(v_a_1056_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
v___x_1064_ = lean_apply_6(v_evalsAtAtoms_x27_1062_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, lean_box(0));
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1085_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1085_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1085_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v_atoms_1070_; lean_object* v_atomsAssignmentCache_1071_; lean_object* v_evalsAtCache_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1084_; 
v___x_1069_ = lean_st_ref_take(v_a_1053_);
v_atoms_1070_ = lean_ctor_get(v___x_1069_, 0);
v_atomsAssignmentCache_1071_ = lean_ctor_get(v___x_1069_, 1);
v_evalsAtCache_1072_ = lean_ctor_get(v___x_1069_, 2);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1074_ = v___x_1069_;
v_isShared_1075_ = v_isSharedCheck_1084_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_evalsAtCache_1072_);
lean_inc(v_atomsAssignmentCache_1071_);
lean_inc(v_atoms_1070_);
lean_dec(v___x_1069_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1084_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_inc(v_a_1065_);
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_1072_, v_originalExpr_1061_, v_a_1065_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 2, v___x_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_atoms_1070_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_atomsAssignmentCache_1071_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_st_ref_set(v_a_1053_, v___x_1078_);
if (v_isShared_1068_ == 0)
{
v___x_1081_ = v___x_1067_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1065_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_1061_);
return v___x_1064_;
}
}
else
{
lean_object* v_val_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v_evalsAtAtoms_x27_1062_);
lean_dec_ref(v_originalExpr_1061_);
v_val_1086_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1063_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_val_1086_);
lean_dec(v___x_1063_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 0);
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_val_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_evalsAtAtoms___boxed(lean_object* v_reified_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_evalsAtAtoms(v_reified_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
return v_res_1101_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_unsigned_to_nat(16u);
v___x_1104_ = lean_mk_array(v___x_1103_, v___x_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__0);
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1105_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1);
v___x_1110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v___x_1108_);
lean_ctor_set(v___x_1110_, 2, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg(lean_object* v_m_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__2);
v___x_1118_ = lean_st_mk_ref(v___x_1117_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
lean_inc(v_a_1113_);
lean_inc_ref(v_a_1112_);
lean_inc(v___x_1118_);
v___x_1119_ = lean_apply_6(v_m_1111_, v___x_1118_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, lean_box(0));
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_st_ref_get(v___x_1118_);
lean_dec(v___x_1118_);
lean_dec(v___x_1124_);
if (v_isShared_1123_ == 0)
{
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1120_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_dec(v___x_1118_);
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___boxed(lean_object* v_m_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg(v_m_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run(lean_object* v_00_u03b1_1136_, lean_object* v_m_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg(v_m_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___boxed(lean_object* v_00_u03b1_1144_, lean_object* v_m_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_run(v_00_u03b1_1144_, v_m_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__2(lean_object* v_x_1152_, lean_object* v_x_1153_){
_start:
{
if (lean_obj_tag(v_x_1153_) == 0)
{
return v_x_1152_;
}
else
{
lean_object* v_key_1154_; lean_object* v_value_1155_; lean_object* v_tail_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_key_1154_ = lean_ctor_get(v_x_1153_, 0);
v_value_1155_ = lean_ctor_get(v_x_1153_, 1);
v_tail_1156_ = lean_ctor_get(v_x_1153_, 2);
lean_inc(v_value_1155_);
lean_inc(v_key_1154_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_key_1154_);
lean_ctor_set(v___x_1157_, 1, v_value_1155_);
v___x_1158_ = lean_array_push(v_x_1152_, v___x_1157_);
v_x_1152_ = v___x_1158_;
v_x_1153_ = v_tail_1156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__2___boxed(lean_object* v_x_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__2(v_x_1160_, v_x_1161_);
lean_dec(v_x_1161_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__3(lean_object* v_as_1163_, size_t v_i_1164_, size_t v_stop_1165_, lean_object* v_b_1166_){
_start:
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_usize_dec_eq(v_i_1164_, v_stop_1165_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; 
v___x_1168_ = lean_array_uget_borrowed(v_as_1163_, v_i_1164_);
v___x_1169_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__2(v_b_1166_, v___x_1168_);
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_add(v_i_1164_, v___x_1170_);
v_i_1164_ = v___x_1171_;
v_b_1166_ = v___x_1169_;
goto _start;
}
else
{
return v_b_1166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__3___boxed(lean_object* v_as_1173_, lean_object* v_i_1174_, lean_object* v_stop_1175_, lean_object* v_b_1176_){
_start:
{
size_t v_i_boxed_1177_; size_t v_stop_boxed_1178_; lean_object* v_res_1179_; 
v_i_boxed_1177_ = lean_unbox_usize(v_i_1174_);
lean_dec(v_i_1174_);
v_stop_boxed_1178_ = lean_unbox_usize(v_stop_1175_);
lean_dec(v_stop_1175_);
v_res_1179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__3(v_as_1173_, v_i_boxed_1177_, v_stop_boxed_1178_, v_b_1176_);
lean_dec_ref(v_as_1173_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1___redArg(lean_object* v_hi_1180_, lean_object* v_pivot_1181_, lean_object* v_as_1182_, lean_object* v_i_1183_, lean_object* v_k_1184_){
_start:
{
uint8_t v___x_1185_; 
v___x_1185_ = lean_nat_dec_lt(v_k_1184_, v_hi_1180_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec(v_k_1184_);
v___x_1186_ = lean_array_fswap(v_as_1182_, v_i_1183_, v_hi_1180_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_i_1183_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; lean_object* v_snd_1189_; lean_object* v_snd_1190_; lean_object* v_atomNumber_1191_; lean_object* v_atomNumber_1192_; uint8_t v___x_1193_; 
v___x_1188_ = lean_array_fget_borrowed(v_as_1182_, v_k_1184_);
v_snd_1189_ = lean_ctor_get(v___x_1188_, 1);
v_snd_1190_ = lean_ctor_get(v_pivot_1181_, 1);
v_atomNumber_1191_ = lean_ctor_get(v_snd_1189_, 1);
v_atomNumber_1192_ = lean_ctor_get(v_snd_1190_, 1);
v___x_1193_ = lean_nat_dec_lt(v_atomNumber_1191_, v_atomNumber_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_add(v_k_1184_, v___x_1194_);
lean_dec(v_k_1184_);
v_k_1184_ = v___x_1195_;
goto _start;
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = lean_array_fswap(v_as_1182_, v_i_1183_, v_k_1184_);
v___x_1198_ = lean_unsigned_to_nat(1u);
v___x_1199_ = lean_nat_add(v_i_1183_, v___x_1198_);
lean_dec(v_i_1183_);
v___x_1200_ = lean_nat_add(v_k_1184_, v___x_1198_);
lean_dec(v_k_1184_);
v_as_1182_ = v___x_1197_;
v_i_1183_ = v___x_1199_;
v_k_1184_ = v___x_1200_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1202_, lean_object* v_pivot_1203_, lean_object* v_as_1204_, lean_object* v_i_1205_, lean_object* v_k_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1___redArg(v_hi_1202_, v_pivot_1203_, v_as_1204_, v_i_1205_, v_k_1206_);
lean_dec_ref(v_pivot_1203_);
lean_dec(v_hi_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0(lean_object* v_x1_1208_, lean_object* v_x2_1209_){
_start:
{
lean_object* v_snd_1210_; lean_object* v_snd_1211_; lean_object* v_atomNumber_1212_; lean_object* v_atomNumber_1213_; uint8_t v___x_1214_; 
v_snd_1210_ = lean_ctor_get(v_x1_1208_, 1);
v_snd_1211_ = lean_ctor_get(v_x2_1209_, 1);
v_atomNumber_1212_ = lean_ctor_get(v_snd_1210_, 1);
v_atomNumber_1213_ = lean_ctor_get(v_snd_1211_, 1);
v___x_1214_ = lean_nat_dec_lt(v_atomNumber_1212_, v_atomNumber_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0___boxed(lean_object* v_x1_1215_, lean_object* v_x2_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0(v_x1_1215_, v_x2_1216_);
lean_dec_ref(v_x2_1216_);
lean_dec_ref(v_x1_1215_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(lean_object* v_n_1219_, lean_object* v_as_1220_, lean_object* v_lo_1221_, lean_object* v_hi_1222_){
_start:
{
lean_object* v___y_1224_; uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_lt(v_lo_1221_, v_hi_1222_);
if (v___x_1234_ == 0)
{
lean_dec(v_lo_1221_);
return v_as_1220_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_mid_1237_; lean_object* v___y_1239_; lean_object* v___y_1245_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1235_ = lean_nat_add(v_lo_1221_, v_hi_1222_);
v___x_1236_ = lean_unsigned_to_nat(1u);
v_mid_1237_ = lean_nat_shiftr(v___x_1235_, v___x_1236_);
lean_dec(v___x_1235_);
v___x_1250_ = lean_array_fget_borrowed(v_as_1220_, v_mid_1237_);
v___x_1251_ = lean_array_fget_borrowed(v_as_1220_, v_lo_1221_);
v___x_1252_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
v___y_1245_ = v_as_1220_;
goto v___jp_1244_;
}
else
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_array_fswap(v_as_1220_, v_lo_1221_, v_mid_1237_);
v___y_1245_ = v___x_1253_;
goto v___jp_1244_;
}
v___jp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = lean_array_fget_borrowed(v___y_1239_, v_mid_1237_);
v___x_1241_ = lean_array_fget_borrowed(v___y_1239_, v_hi_1222_);
v___x_1242_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec(v_mid_1237_);
v___y_1224_ = v___y_1239_;
goto v___jp_1223_;
}
else
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_array_fswap(v___y_1239_, v_mid_1237_, v_hi_1222_);
lean_dec(v_mid_1237_);
v___y_1224_ = v___x_1243_;
goto v___jp_1223_;
}
}
v___jp_1244_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1246_ = lean_array_fget_borrowed(v___y_1245_, v_hi_1222_);
v___x_1247_ = lean_array_fget_borrowed(v___y_1245_, v_lo_1221_);
v___x_1248_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
v___y_1239_ = v___y_1245_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_array_fswap(v___y_1245_, v_lo_1221_, v_hi_1222_);
v___y_1239_ = v___x_1249_;
goto v___jp_1238_;
}
}
}
v___jp_1223_:
{
lean_object* v_pivot_1225_; lean_object* v___x_1226_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; uint8_t v___x_1229_; 
v_pivot_1225_ = lean_array_fget(v___y_1224_, v_hi_1222_);
lean_inc_n(v_lo_1221_, 2);
v___x_1226_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1___redArg(v_hi_1222_, v_pivot_1225_, v___y_1224_, v_lo_1221_, v_lo_1221_);
lean_dec(v_pivot_1225_);
v_fst_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_fst_1227_);
v_snd_1228_ = lean_ctor_get(v___x_1226_, 1);
lean_inc(v_snd_1228_);
lean_dec_ref(v___x_1226_);
v___x_1229_ = lean_nat_dec_le(v_hi_1222_, v_fst_1227_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(v_n_1219_, v_snd_1228_, v_lo_1221_, v_fst_1227_);
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_add(v_fst_1227_, v___x_1231_);
lean_dec(v_fst_1227_);
v_as_1220_ = v___x_1230_;
v_lo_1221_ = v___x_1232_;
goto _start;
}
else
{
lean_dec(v_fst_1227_);
lean_dec(v_lo_1221_);
return v_snd_1228_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___boxed(lean_object* v_n_1254_, lean_object* v_as_1255_, lean_object* v_lo_1256_, lean_object* v_hi_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(v_n_1254_, v_as_1255_, v_lo_1256_, v_hi_1257_);
lean_dec(v_hi_1257_);
lean_dec(v_n_1254_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0(size_t v_sz_1259_, size_t v_i_1260_, lean_object* v_bs_1261_){
_start:
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_usize_dec_lt(v_i_1260_, v_sz_1259_);
if (v___x_1262_ == 0)
{
return v_bs_1261_;
}
else
{
lean_object* v_v_1263_; lean_object* v_snd_1264_; lean_object* v_fst_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1279_; 
v_v_1263_ = lean_array_uget(v_bs_1261_, v_i_1260_);
v_snd_1264_ = lean_ctor_get(v_v_1263_, 1);
v_fst_1265_ = lean_ctor_get(v_v_1263_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_v_1263_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1267_ = v_v_1263_;
v_isShared_1268_ = v_isSharedCheck_1279_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_snd_1264_);
lean_inc(v_fst_1265_);
lean_dec(v_v_1263_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1279_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v_width_1269_; lean_object* v___x_1270_; lean_object* v_bs_x27_1271_; lean_object* v___x_1273_; 
v_width_1269_ = lean_ctor_get(v_snd_1264_, 0);
lean_inc(v_width_1269_);
lean_dec(v_snd_1264_);
v___x_1270_ = lean_unsigned_to_nat(0u);
v_bs_x27_1271_ = lean_array_uset(v_bs_1261_, v_i_1260_, v___x_1270_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v_fst_1265_);
lean_ctor_set(v___x_1267_, 0, v_width_1269_);
v___x_1273_ = v___x_1267_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_width_1269_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_fst_1265_);
v___x_1273_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = ((size_t)1ULL);
v___x_1275_ = lean_usize_add(v_i_1260_, v___x_1274_);
v___x_1276_ = lean_array_uset(v_bs_x27_1271_, v_i_1260_, v___x_1273_);
v_i_1260_ = v___x_1275_;
v_bs_1261_ = v___x_1276_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0___boxed(lean_object* v_sz_1280_, lean_object* v_i_1281_, lean_object* v_bs_1282_){
_start:
{
size_t v_sz_boxed_1283_; size_t v_i_boxed_1284_; lean_object* v_res_1285_; 
v_sz_boxed_1283_ = lean_unbox_usize(v_sz_1280_);
lean_dec(v_sz_1280_);
v_i_boxed_1284_ = lean_unbox_usize(v_i_1281_);
lean_dec(v_i_1281_);
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0(v_sz_boxed_1283_, v_i_boxed_1284_, v_bs_1282_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg(lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1288_; lean_object* v___y_1290_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1308_; lean_object* v_atoms_1315_; lean_object* v_size_1316_; lean_object* v_buckets_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1288_ = lean_st_ref_get(v_a_1286_);
v_atoms_1315_ = lean_ctor_get(v___x_1288_, 0);
lean_inc_ref(v_atoms_1315_);
lean_dec(v___x_1288_);
v_size_1316_ = lean_ctor_get(v_atoms_1315_, 0);
lean_inc(v_size_1316_);
v_buckets_1317_ = lean_ctor_get(v_atoms_1315_, 1);
lean_inc_ref(v_buckets_1317_);
lean_dec_ref(v_atoms_1315_);
v___x_1318_ = lean_mk_empty_array_with_capacity(v_size_1316_);
lean_dec(v_size_1316_);
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = lean_array_get_size(v_buckets_1317_);
v___x_1321_ = lean_nat_dec_lt(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_dec_ref(v_buckets_1317_);
v___y_1308_ = v___x_1318_;
goto v___jp_1307_;
}
else
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_nat_dec_le(v___x_1320_, v___x_1320_);
if (v___x_1322_ == 0)
{
if (v___x_1321_ == 0)
{
lean_dec_ref(v_buckets_1317_);
v___y_1308_ = v___x_1318_;
goto v___jp_1307_;
}
else
{
size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = lean_usize_of_nat(v___x_1320_);
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__3(v_buckets_1317_, v___x_1323_, v___x_1324_, v___x_1318_);
lean_dec_ref(v_buckets_1317_);
v___y_1308_ = v___x_1325_;
goto v___jp_1307_;
}
}
else
{
size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = ((size_t)0ULL);
v___x_1327_ = lean_usize_of_nat(v___x_1320_);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__3(v_buckets_1317_, v___x_1326_, v___x_1327_, v___x_1318_);
lean_dec_ref(v_buckets_1317_);
v___y_1308_ = v___x_1328_;
goto v___jp_1307_;
}
}
v___jp_1289_:
{
size_t v_sz_1291_; size_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_sz_1291_ = lean_array_size(v___y_1290_);
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0(v_sz_1291_, v___x_1292_, v___y_1290_);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
v___jp_1295_:
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec(v___y_1296_);
v___y_1290_ = v___x_1300_;
goto v___jp_1289_;
}
v___jp_1301_:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_nat_dec_le(v___y_1305_, v___y_1302_);
if (v___x_1306_ == 0)
{
lean_dec(v___y_1302_);
lean_inc(v___y_1305_);
v___y_1296_ = v___y_1303_;
v___y_1297_ = v___y_1304_;
v___y_1298_ = v___y_1305_;
v___y_1299_ = v___y_1305_;
goto v___jp_1295_;
}
else
{
v___y_1296_ = v___y_1303_;
v___y_1297_ = v___y_1304_;
v___y_1298_ = v___y_1305_;
v___y_1299_ = v___y_1302_;
goto v___jp_1295_;
}
}
v___jp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1309_ = lean_array_get_size(v___y_1308_);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_nat_dec_eq(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1312_ = lean_unsigned_to_nat(1u);
v___x_1313_ = lean_nat_sub(v___x_1309_, v___x_1312_);
v___x_1314_ = lean_nat_dec_le(v___x_1310_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_inc(v___x_1313_);
v___y_1302_ = v___x_1313_;
v___y_1303_ = v___x_1309_;
v___y_1304_ = v___y_1308_;
v___y_1305_ = v___x_1313_;
goto v___jp_1301_;
}
else
{
v___y_1302_ = v___x_1313_;
v___y_1303_ = v___x_1309_;
v___y_1304_ = v___y_1308_;
v___y_1305_ = v___x_1310_;
goto v___jp_1301_;
}
}
else
{
v___y_1290_ = v___y_1308_;
goto v___jp_1289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg___boxed(lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg(v_a_1329_);
lean_dec(v_a_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms(lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg(v_a_1332_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___boxed(lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms(v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1(lean_object* v_n_1346_, lean_object* v_as_1347_, lean_object* v_lo_1348_, lean_object* v_hi_1349_, lean_object* v_w_1350_, lean_object* v_hlo_1351_, lean_object* v_hhi_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(v_n_1346_, v_as_1347_, v_lo_1348_, v_hi_1349_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___boxed(lean_object* v_n_1354_, lean_object* v_as_1355_, lean_object* v_lo_1356_, lean_object* v_hi_1357_, lean_object* v_w_1358_, lean_object* v_hlo_1359_, lean_object* v_hhi_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1(v_n_1354_, v_as_1355_, v_lo_1356_, v_hi_1357_, v_w_1358_, v_hlo_1359_, v_hhi_1360_);
lean_dec(v_hi_1357_);
lean_dec(v_n_1354_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1(lean_object* v_n_1362_, lean_object* v_lo_1363_, lean_object* v_hi_1364_, lean_object* v_hhi_1365_, lean_object* v_pivot_1366_, lean_object* v_as_1367_, lean_object* v_i_1368_, lean_object* v_k_1369_, lean_object* v_ilo_1370_, lean_object* v_ik_1371_, lean_object* v_w_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1___redArg(v_hi_1364_, v_pivot_1366_, v_as_1367_, v_i_1368_, v_k_1369_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1___boxed(lean_object* v_n_1374_, lean_object* v_lo_1375_, lean_object* v_hi_1376_, lean_object* v_hhi_1377_, lean_object* v_pivot_1378_, lean_object* v_as_1379_, lean_object* v_i_1380_, lean_object* v_k_1381_, lean_object* v_ilo_1382_, lean_object* v_ik_1383_, lean_object* v_w_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1_spec__1(v_n_1374_, v_lo_1375_, v_hi_1376_, v_hhi_1377_, v_pivot_1378_, v_as_1379_, v_i_1380_, v_k_1381_, v_ilo_1382_, v_ik_1383_, v_w_1384_);
lean_dec_ref(v_pivot_1378_);
lean_dec(v_hi_1376_);
lean_dec(v_lo_1375_);
lean_dec(v_n_1374_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___lam__0(lean_object* v___x_1387_, lean_object* v___x_1388_, lean_object* v___x_1389_, lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v_fst_1394_ = lean_ctor_get(v_x_1393_, 0);
lean_inc(v_fst_1394_);
v_snd_1395_ = lean_ctor_get(v_x_1393_, 1);
lean_inc(v_snd_1395_);
lean_dec_ref(v_x_1393_);
v___x_1396_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0));
v___x_1397_ = l_Lean_Name_mkStr6(v___x_1387_, v___x_1388_, v___x_1389_, v___x_1390_, v___x_1391_, v___x_1396_);
v___x_1398_ = l_Lean_mkConst(v___x_1397_, v___x_1392_);
v___x_1399_ = l_Lean_mkNatLit(v_fst_1394_);
v___x_1400_ = l_Lean_mkAppB(v___x_1398_, v___x_1399_, v_snd_1395_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(lean_object* v_msgData_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; lean_object* v_env_1408_; lean_object* v___x_1409_; lean_object* v_mctx_1410_; lean_object* v_lctx_1411_; lean_object* v_options_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1407_ = lean_st_ref_get(v___y_1405_);
v_env_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc_ref(v_env_1408_);
lean_dec(v___x_1407_);
v___x_1409_ = lean_st_ref_get(v___y_1403_);
v_mctx_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc_ref(v_mctx_1410_);
lean_dec(v___x_1409_);
v_lctx_1411_ = lean_ctor_get(v___y_1402_, 2);
v_options_1412_ = lean_ctor_get(v___y_1404_, 2);
lean_inc_ref(v_options_1412_);
lean_inc_ref(v_lctx_1411_);
v___x_1413_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1413_, 0, v_env_1408_);
lean_ctor_set(v___x_1413_, 1, v_mctx_1410_);
lean_ctor_set(v___x_1413_, 2, v_lctx_1411_);
lean_ctor_set(v___x_1413_, 3, v_options_1412_);
v___x_1414_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v_msgData_1401_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0___boxed(lean_object* v_msgData_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msgData_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_ref_1429_; lean_object* v___x_1430_; lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1439_; 
v_ref_1429_ = lean_ctor_get(v___y_1426_, 5);
v___x_1430_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msg_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_inc(v_ref_1429_);
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_ref_1429_);
lean_ctor_set(v___x_1435_, 1, v_a_1431_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set_tag(v___x_1433_, 1);
lean_ctor_set(v___x_1433_, 0, v___x_1435_);
v___x_1437_ = v___x_1433_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg___boxed(lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v_msg_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1446_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__1(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__0));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__5(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = lean_box(0);
v___x_1465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3));
v___x_1466_ = l_Lean_mkConst(v___x_1465_, v___x_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment(lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1510_; 
v___x_1473_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg(v_a_1467_);
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1510_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1510_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_array_get_size(v_a_1474_);
v___x_1480_ = lean_nat_dec_lt(v___x_1478_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_del_object(v___x_1476_);
lean_dec(v_a_1474_);
v___x_1481_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__1);
v___x_1482_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v___x_1481_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; lean_object* v___f_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1483_ = l_Lean_RArray_ofArray___redArg(v_a_1474_);
v___f_1484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__4));
v___x_1485_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__5, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__5_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__5);
v___x_1486_ = l_Lean_RArray_toExpr___redArg(v___x_1485_, v___f_1484_, v___x_1483_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1509_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1509_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1509_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v_atoms_1492_; lean_object* v_evalsAtCache_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1507_; 
v___x_1491_ = lean_st_ref_take(v_a_1467_);
v_atoms_1492_ = lean_ctor_get(v___x_1491_, 0);
v_evalsAtCache_1493_ = lean_ctor_get(v___x_1491_, 2);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v___x_1491_, 1);
lean_dec(v_unused_1508_);
v___x_1495_ = v___x_1491_;
v_isShared_1496_ = v_isSharedCheck_1507_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_evalsAtCache_1493_);
lean_inc(v_atoms_1492_);
lean_dec(v___x_1491_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1507_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
lean_inc(v_a_1487_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set_tag(v___x_1476_, 1);
lean_ctor_set(v___x_1476_, 0, v_a_1487_);
v___x_1498_ = v___x_1476_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1487_);
v___x_1498_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1498_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_atoms_1492_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1505_, 2, v_evalsAtCache_1493_);
v___x_1500_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = lean_st_ref_set(v_a_1467_, v___x_1500_);
if (v_isShared_1490_ == 0)
{
v___x_1503_ = v___x_1489_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1487_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1476_);
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___boxed(lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment(v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0(lean_object* v_00_u03b1_1518_, lean_object* v_msg_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v_msg_1519_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___boxed(lean_object* v_00_u03b1_1527_, lean_object* v_msg_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0(v_00_u03b1_1527_, v_msg_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment(lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v_atomsAssignmentCache_1543_; 
v___x_1542_ = lean_st_ref_get(v_a_1536_);
v_atomsAssignmentCache_1543_ = lean_ctor_get(v___x_1542_, 1);
lean_inc(v_atomsAssignmentCache_1543_);
lean_dec(v___x_1542_);
if (lean_obj_tag(v_atomsAssignmentCache_1543_) == 0)
{
lean_object* v___x_1544_; 
v___x_1544_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment(v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
return v___x_1544_;
}
else
{
lean_object* v_val_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
v_val_1545_ = lean_ctor_get(v_atomsAssignmentCache_1543_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_atomsAssignmentCache_1543_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v_atomsAssignmentCache_1543_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_val_1545_);
lean_dec(v_atomsAssignmentCache_1543_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 0);
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_val_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment___boxed(lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment(v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
return v_res_1559_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_instMonadEIO(lean_box(0));
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1(lean_object* v_msg_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v_toApplicative_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1636_; 
v___x_1572_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__0, &l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__0);
v___x_1573_ = l_StateRefT_x27_instMonad___redArg(v___x_1572_);
v_toApplicative_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1636_ == 0)
{
lean_object* v_unused_1637_; 
v_unused_1637_ = lean_ctor_get(v___x_1573_, 1);
lean_dec(v_unused_1637_);
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1636_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_toApplicative_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1636_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_toFunctor_1578_; lean_object* v_toSeq_1579_; lean_object* v_toSeqLeft_1580_; lean_object* v_toSeqRight_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1634_; 
v_toFunctor_1578_ = lean_ctor_get(v_toApplicative_1574_, 0);
v_toSeq_1579_ = lean_ctor_get(v_toApplicative_1574_, 2);
v_toSeqLeft_1580_ = lean_ctor_get(v_toApplicative_1574_, 3);
v_toSeqRight_1581_ = lean_ctor_get(v_toApplicative_1574_, 4);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_toApplicative_1574_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v_toApplicative_1574_, 1);
lean_dec(v_unused_1635_);
v___x_1583_ = v_toApplicative_1574_;
v_isShared_1584_ = v_isSharedCheck_1634_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_toSeqRight_1581_);
lean_inc(v_toSeqLeft_1580_);
lean_inc(v_toSeq_1579_);
lean_inc(v_toFunctor_1578_);
lean_dec(v_toApplicative_1574_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1634_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___f_1585_; lean_object* v___f_1586_; lean_object* v___f_1587_; lean_object* v___f_1588_; lean_object* v___x_1589_; lean_object* v___f_1590_; lean_object* v___f_1591_; lean_object* v___f_1592_; lean_object* v___x_1594_; 
v___f_1585_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__1));
v___f_1586_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1578_);
v___f_1587_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1587_, 0, v_toFunctor_1578_);
v___f_1588_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1588_, 0, v_toFunctor_1578_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___f_1587_);
lean_ctor_set(v___x_1589_, 1, v___f_1588_);
v___f_1590_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1590_, 0, v_toSeqRight_1581_);
v___f_1591_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1591_, 0, v_toSeqLeft_1580_);
v___f_1592_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1592_, 0, v_toSeq_1579_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v___f_1590_);
lean_ctor_set(v___x_1583_, 3, v___f_1591_);
lean_ctor_set(v___x_1583_, 2, v___f_1592_);
lean_ctor_set(v___x_1583_, 1, v___f_1585_);
lean_ctor_set(v___x_1583_, 0, v___x_1589_);
v___x_1594_ = v___x_1583_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v___f_1585_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v___f_1592_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v___f_1591_);
lean_ctor_set(v_reuseFailAlloc_1633_, 4, v___f_1590_);
v___x_1594_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v___f_1586_);
lean_ctor_set(v___x_1576_, 0, v___x_1594_);
v___x_1596_ = v___x_1576_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v___f_1586_);
v___x_1596_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; lean_object* v_toApplicative_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1630_; 
v___x_1597_ = l_StateRefT_x27_instMonad___redArg(v___x_1596_);
v_toApplicative_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v___x_1597_, 1);
lean_dec(v_unused_1631_);
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1630_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_toApplicative_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1630_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_toFunctor_1602_; lean_object* v_toSeq_1603_; lean_object* v_toSeqLeft_1604_; lean_object* v_toSeqRight_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1628_; 
v_toFunctor_1602_ = lean_ctor_get(v_toApplicative_1598_, 0);
v_toSeq_1603_ = lean_ctor_get(v_toApplicative_1598_, 2);
v_toSeqLeft_1604_ = lean_ctor_get(v_toApplicative_1598_, 3);
v_toSeqRight_1605_ = lean_ctor_get(v_toApplicative_1598_, 4);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_toApplicative_1598_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; 
v_unused_1629_ = lean_ctor_get(v_toApplicative_1598_, 1);
lean_dec(v_unused_1629_);
v___x_1607_ = v_toApplicative_1598_;
v_isShared_1608_ = v_isSharedCheck_1628_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_toSeqRight_1605_);
lean_inc(v_toSeqLeft_1604_);
lean_inc(v_toSeq_1603_);
lean_inc(v_toFunctor_1602_);
lean_dec(v_toApplicative_1598_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1628_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___f_1609_; lean_object* v___f_1610_; lean_object* v___f_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; lean_object* v___f_1614_; lean_object* v___f_1615_; lean_object* v___f_1616_; lean_object* v___x_1618_; 
v___f_1609_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__3));
v___f_1610_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1602_);
v___f_1611_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1611_, 0, v_toFunctor_1602_);
v___f_1612_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1612_, 0, v_toFunctor_1602_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___f_1611_);
lean_ctor_set(v___x_1613_, 1, v___f_1612_);
v___f_1614_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1614_, 0, v_toSeqRight_1605_);
v___f_1615_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1615_, 0, v_toSeqLeft_1604_);
v___f_1616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1616_, 0, v_toSeq_1603_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 4, v___f_1614_);
lean_ctor_set(v___x_1607_, 3, v___f_1615_);
lean_ctor_set(v___x_1607_, 2, v___f_1616_);
lean_ctor_set(v___x_1607_, 1, v___f_1609_);
lean_ctor_set(v___x_1607_, 0, v___x_1613_);
v___x_1618_ = v___x_1607_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v___f_1609_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v___f_1616_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v___f_1615_);
lean_ctor_set(v_reuseFailAlloc_1627_, 4, v___f_1614_);
v___x_1618_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1620_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 1, v___f_1610_);
lean_ctor_set(v___x_1600_, 0, v___x_1618_);
v___x_1620_ = v___x_1600_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v___f_1610_);
v___x_1620_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_4521__overap_1624_; lean_object* v___x_1625_; 
v___x_1621_ = l_StateRefT_x27_instMonad___redArg(v___x_1620_);
v___x_1622_ = lean_box(0);
v___x_1623_ = l_instInhabitedOfMonad___redArg(v___x_1621_, v___x_1622_);
v___x_4521__overap_1624_ = lean_panic_fn_borrowed(v___x_1623_, v_msg_1565_);
lean_dec(v___x_1623_);
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
lean_inc(v___y_1566_);
v___x_1625_ = lean_apply_6(v___x_4521__overap_1624_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, lean_box(0));
return v___x_1625_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___boxed(lean_object* v_msg_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1(v_msg_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
return v_res_1645_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1646_; double v___x_1647_; 
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = lean_float_of_nat(v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(lean_object* v_cls_1651_, lean_object* v_msg_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_ref_1658_; lean_object* v___x_1659_; lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1704_; 
v_ref_1658_ = lean_ctor_get(v___y_1655_, 5);
v___x_1659_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msg_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1704_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1704_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v_traceState_1665_; lean_object* v_env_1666_; lean_object* v_nextMacroScope_1667_; lean_object* v_ngen_1668_; lean_object* v_auxDeclNGen_1669_; lean_object* v_cache_1670_; lean_object* v_messages_1671_; lean_object* v_infoState_1672_; lean_object* v_snapshotTasks_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1703_; 
v___x_1664_ = lean_st_ref_take(v___y_1656_);
v_traceState_1665_ = lean_ctor_get(v___x_1664_, 4);
v_env_1666_ = lean_ctor_get(v___x_1664_, 0);
v_nextMacroScope_1667_ = lean_ctor_get(v___x_1664_, 1);
v_ngen_1668_ = lean_ctor_get(v___x_1664_, 2);
v_auxDeclNGen_1669_ = lean_ctor_get(v___x_1664_, 3);
v_cache_1670_ = lean_ctor_get(v___x_1664_, 5);
v_messages_1671_ = lean_ctor_get(v___x_1664_, 6);
v_infoState_1672_ = lean_ctor_get(v___x_1664_, 7);
v_snapshotTasks_1673_ = lean_ctor_get(v___x_1664_, 8);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1675_ = v___x_1664_;
v_isShared_1676_ = v_isSharedCheck_1703_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_snapshotTasks_1673_);
lean_inc(v_infoState_1672_);
lean_inc(v_messages_1671_);
lean_inc(v_cache_1670_);
lean_inc(v_traceState_1665_);
lean_inc(v_auxDeclNGen_1669_);
lean_inc(v_ngen_1668_);
lean_inc(v_nextMacroScope_1667_);
lean_inc(v_env_1666_);
lean_dec(v___x_1664_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1703_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
uint64_t v_tid_1677_; lean_object* v_traces_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1702_; 
v_tid_1677_ = lean_ctor_get_uint64(v_traceState_1665_, sizeof(void*)*1);
v_traces_1678_ = lean_ctor_get(v_traceState_1665_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_traceState_1665_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1680_ = v_traceState_1665_;
v_isShared_1681_ = v_isSharedCheck_1702_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_traces_1678_);
lean_dec(v_traceState_1665_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1702_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; double v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1682_ = lean_box(0);
v___x_1683_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__0);
v___x_1684_ = 0;
v___x_1685_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__1));
v___x_1686_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1686_, 0, v_cls_1651_);
lean_ctor_set(v___x_1686_, 1, v___x_1682_);
lean_ctor_set(v___x_1686_, 2, v___x_1685_);
lean_ctor_set_float(v___x_1686_, sizeof(void*)*3, v___x_1683_);
lean_ctor_set_float(v___x_1686_, sizeof(void*)*3 + 8, v___x_1683_);
lean_ctor_set_uint8(v___x_1686_, sizeof(void*)*3 + 16, v___x_1684_);
v___x_1687_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__2));
v___x_1688_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v_a_1660_);
lean_ctor_set(v___x_1688_, 2, v___x_1687_);
lean_inc(v_ref_1658_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_ref_1658_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = l_Lean_PersistentArray_push___redArg(v_traces_1678_, v___x_1689_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1690_);
v___x_1692_ = v___x_1680_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1690_);
lean_ctor_set_uint64(v_reuseFailAlloc_1701_, sizeof(void*)*1, v_tid_1677_);
v___x_1692_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1694_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 4, v___x_1692_);
v___x_1694_ = v___x_1675_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_env_1666_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_nextMacroScope_1667_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_ngen_1668_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_auxDeclNGen_1669_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1700_, 5, v_cache_1670_);
lean_ctor_set(v_reuseFailAlloc_1700_, 6, v_messages_1671_);
lean_ctor_set(v_reuseFailAlloc_1700_, 7, v_infoState_1672_);
lean_ctor_set(v_reuseFailAlloc_1700_, 8, v_snapshotTasks_1673_);
v___x_1694_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1695_ = lean_st_ref_set(v___y_1656_, v___x_1694_);
v___x_1696_ = lean_box(0);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1696_);
v___x_1698_ = v___x_1662_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___boxed(lean_object* v_cls_1705_, lean_object* v_msg_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(v_cls_1705_, v_msg_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
return v_res_1712_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__5(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2));
v___x_1723_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__4));
v___x_1724_ = l_Lean_Name_append(v___x_1723_, v___x_1722_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__7(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__6));
v___x_1727_ = l_Lean_stringToMessageData(v___x_1726_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__9(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__8));
v___x_1730_ = l_Lean_stringToMessageData(v___x_1729_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__11(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__10));
v___x_1733_ = l_Lean_stringToMessageData(v___x_1732_);
return v___x_1733_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__15(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1737_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__14));
v___x_1738_ = lean_unsigned_to_nat(6u);
v___x_1739_ = lean_unsigned_to_nat(310u);
v___x_1740_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__13));
v___x_1741_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__12));
v___x_1742_ = l_mkPanicMessageWithDecl(v___x_1741_, v___x_1740_, v___x_1739_, v___x_1738_, v___x_1737_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup(lean_object* v_e_1743_, lean_object* v_width_1744_, uint8_t v_synthetic_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___y_1753_; lean_object* v___x_1772_; lean_object* v_atoms_1773_; lean_object* v___x_1774_; 
v___x_1772_ = lean_st_ref_get(v_a_1746_);
v_atoms_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc_ref(v_atoms_1773_);
lean_dec(v___x_1772_);
v___x_1774_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_atoms_1773_, v_e_1743_);
lean_dec_ref(v_atoms_1773_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_options_1775_; uint8_t v_hasTrace_1776_; 
v_options_1775_ = lean_ctor_get(v_a_1749_, 2);
v_hasTrace_1776_ = lean_ctor_get_uint8(v_options_1775_, sizeof(void*)*1);
if (v_hasTrace_1776_ == 0)
{
v___y_1753_ = v_a_1746_;
goto v___jp_1752_;
}
else
{
lean_object* v_inheritedTraceOptions_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_inheritedTraceOptions_1777_ = lean_ctor_get(v_a_1749_, 13);
v___x_1778_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2));
v___x_1779_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__5);
v___x_1780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1777_, v_options_1775_, v___x_1779_);
if (v___x_1780_ == 0)
{
v___y_1753_ = v_a_1746_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___y_1789_; 
v___x_1781_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__7);
lean_inc(v_width_1744_);
v___x_1782_ = l_Nat_reprFast(v_width_1744_);
v___x_1783_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
v___x_1784_ = l_Lean_MessageData_ofFormat(v___x_1783_);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1781_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__9);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
if (v_synthetic_1745_ == 0)
{
lean_object* v___x_1806_; 
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__7));
v___y_1789_ = v___x_1806_;
goto v___jp_1788_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__10));
v___y_1789_ = v___x_1807_;
goto v___jp_1788_;
}
v___jp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_inc_ref(v___y_1789_);
v___x_1790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___y_1789_);
v___x_1791_ = l_Lean_MessageData_ofFormat(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1787_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__11);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
lean_inc_ref(v_e_1743_);
v___x_1795_ = l_Lean_MessageData_ofExpr(v_e_1743_);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(v___x_1778_, v___x_1796_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_dec_ref(v___x_1797_);
v___y_1753_ = v_a_1746_;
goto v___jp_1752_;
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_width_1744_);
lean_dec_ref(v_e_1743_);
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v_e_1743_);
v_val_1808_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1810_ = v___x_1774_;
v_isShared_1811_ = v_isSharedCheck_1836_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_val_1808_);
lean_dec(v___x_1774_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1836_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_width_1812_; lean_object* v_atomNumber_1813_; uint8_t v___x_1814_; 
v_width_1812_ = lean_ctor_get(v_val_1808_, 0);
lean_inc(v_width_1812_);
v_atomNumber_1813_ = lean_ctor_get(v_val_1808_, 1);
lean_inc(v_atomNumber_1813_);
lean_dec(v_val_1808_);
v___x_1814_ = lean_nat_dec_eq(v_width_1744_, v_width_1812_);
lean_dec(v_width_1812_);
lean_dec(v_width_1744_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_del_object(v___x_1810_);
v___x_1815_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__15);
v___x_1816_ = l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1(v___x_1815_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v___x_1816_, 0);
lean_dec(v_unused_1824_);
v___x_1818_ = v___x_1816_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_dec(v___x_1816_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v_atomNumber_1813_);
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_atomNumber_1813_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_atomNumber_1813_);
v_a_1825_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1816_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1816_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
else
{
lean_object* v___x_1834_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set_tag(v___x_1810_, 0);
lean_ctor_set(v___x_1810_, 0, v_atomNumber_1813_);
v___x_1834_ = v___x_1810_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_atomNumber_1813_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
v___jp_1752_:
{
lean_object* v___x_1754_; lean_object* v_atoms_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1769_; 
v___x_1754_ = lean_st_ref_take(v___y_1753_);
v_atoms_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; lean_object* v_unused_1771_; 
v_unused_1770_ = lean_ctor_get(v___x_1754_, 2);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v___x_1754_, 1);
lean_dec(v_unused_1771_);
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1769_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_atoms_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1769_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_size_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v_size_1759_ = lean_ctor_get(v_atoms_1755_, 0);
lean_inc_n(v_size_1759_, 2);
v___x_1760_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1760_, 0, v_width_1744_);
lean_ctor_set(v___x_1760_, 1, v_size_1759_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*2, v_synthetic_1745_);
v___x_1761_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_atoms_1755_, v_e_1743_, v___x_1760_);
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 2, v___x_1763_);
lean_ctor_set(v___x_1757_, 1, v___x_1762_);
lean_ctor_set(v___x_1757_, 0, v___x_1761_);
v___x_1765_ = v___x_1757_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_st_ref_set(v___y_1753_, v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_size_1759_);
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___boxed(lean_object* v_e_1837_, lean_object* v_width_1838_, lean_object* v_synthetic_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
uint8_t v_synthetic_boxed_1846_; lean_object* v_res_1847_; 
v_synthetic_boxed_1846_ = lean_unbox(v_synthetic_1839_);
v_res_1847_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup(v_e_1837_, v_width_1838_, v_synthetic_boxed_1846_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0(lean_object* v_cls_1848_, lean_object* v_msg_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(v_cls_1848_, v_msg_1849_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___boxed(lean_object* v_cls_1857_, lean_object* v_msg_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0(v_cls_1857_, v_msg_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27(lean_object* v_mkFRefl_1866_, lean_object* v_fst_1867_, lean_object* v_fproof_1868_, lean_object* v_mkSRefl_1869_, lean_object* v_snd_1870_, lean_object* v_sproof_1871_){
_start:
{
if (lean_obj_tag(v_fproof_1868_) == 0)
{
lean_dec_ref(v_snd_1870_);
lean_dec_ref(v_mkSRefl_1869_);
if (lean_obj_tag(v_sproof_1871_) == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v_fst_1867_);
lean_dec_ref(v_mkFRefl_1866_);
v___x_1872_ = lean_box(0);
return v___x_1872_;
}
else
{
lean_object* v_val_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1882_; 
v_val_1873_ = lean_ctor_get(v_sproof_1871_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_sproof_1871_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1875_ = v_sproof_1871_;
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_val_1873_);
lean_dec(v_sproof_1871_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1877_ = lean_apply_1(v_mkFRefl_1866_, v_fst_1867_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v_val_1873_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1878_);
v___x_1880_ = v___x_1875_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_dec_ref(v_fst_1867_);
lean_dec_ref(v_mkFRefl_1866_);
if (lean_obj_tag(v_sproof_1871_) == 0)
{
lean_object* v_val_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1892_; 
v_val_1883_ = lean_ctor_get(v_fproof_1868_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_fproof_1868_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1885_ = v_fproof_1868_;
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_val_1883_);
lean_dec(v_fproof_1868_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1887_ = lean_apply_1(v_mkSRefl_1869_, v_snd_1870_);
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v_val_1883_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
else
{
lean_object* v_val_1893_; lean_object* v_val_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1902_; 
lean_dec_ref(v_snd_1870_);
lean_dec_ref(v_mkSRefl_1869_);
v_val_1893_ = lean_ctor_get(v_fproof_1868_, 0);
lean_inc(v_val_1893_);
lean_dec_ref(v_fproof_1868_);
v_val_1894_ = lean_ctor_get(v_sproof_1871_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_sproof_1871_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1896_ = v_sproof_1871_;
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_val_1894_);
lean_dec(v_sproof_1871_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_val_1893_);
lean_ctor_set(v___x_1898_, 1, v_val_1894_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof(lean_object* v_mkRefl_1903_, lean_object* v_fst_1904_, lean_object* v_fproof_1905_, lean_object* v_snd_1906_, lean_object* v_sproof_1907_){
_start:
{
lean_object* v___x_1908_; 
lean_inc_ref(v_mkRefl_1903_);
v___x_1908_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27(v_mkRefl_1903_, v_fst_1904_, v_fproof_1905_, v_mkRefl_1903_, v_snd_1906_, v_sproof_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyTernaryProof(lean_object* v_mkRefl_1909_, lean_object* v_fst_1910_, lean_object* v_fproof_1911_, lean_object* v_snd_1912_, lean_object* v_sproof_1913_, lean_object* v_thd_1914_, lean_object* v_tproof_1915_){
_start:
{
if (lean_obj_tag(v_fproof_1911_) == 0)
{
lean_object* v___x_1916_; 
lean_inc_ref_n(v_mkRefl_1909_, 2);
v___x_1916_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27(v_mkRefl_1909_, v_snd_1912_, v_sproof_1913_, v_mkRefl_1909_, v_thd_1914_, v_tproof_1915_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1917_; 
lean_dec_ref(v_fst_1910_);
lean_dec_ref(v_mkRefl_1909_);
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
else
{
lean_object* v_val_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1927_; 
v_val_1918_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1920_ = v___x_1916_;
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_val_1918_);
lean_dec(v___x_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1922_ = lean_apply_1(v_mkRefl_1909_, v_fst_1910_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v_val_1918_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1923_);
v___x_1925_ = v___x_1920_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_val_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v_fst_1910_);
v_val_1928_ = lean_ctor_get(v_fproof_1911_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_fproof_1911_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1930_ = v_fproof_1911_;
v_isShared_1931_ = v_isSharedCheck_1949_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_val_1928_);
lean_dec(v_fproof_1911_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1949_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; 
lean_inc_ref(v_thd_1914_);
lean_inc_ref(v_snd_1912_);
lean_inc_ref_n(v_mkRefl_1909_, 2);
v___x_1932_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27(v_mkRefl_1909_, v_snd_1912_, v_sproof_1913_, v_mkRefl_1909_, v_thd_1914_, v_tproof_1915_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
lean_inc_ref(v_mkRefl_1909_);
v___x_1933_ = lean_apply_1(v_mkRefl_1909_, v_snd_1912_);
v___x_1934_ = lean_apply_1(v_mkRefl_1909_, v_thd_1914_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v_val_1928_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1936_);
v___x_1938_ = v___x_1930_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
else
{
lean_object* v_val_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1948_; 
lean_del_object(v___x_1930_);
lean_dec_ref(v_thd_1914_);
lean_dec_ref(v_snd_1912_);
lean_dec_ref(v_mkRefl_1909_);
v_val_1940_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1942_ = v___x_1932_;
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_val_1940_);
lean_dec(v___x_1932_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_val_1928_);
lean_ctor_set(v___x_1944_, 1, v_val_1940_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1944_);
v___x_1946_ = v___x_1942_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg(lean_object* v_m_1950_, lean_object* v_state_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = lean_st_mk_ref(v_state_1951_);
lean_inc(v_a_1956_);
lean_inc_ref(v_a_1955_);
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc(v_a_1952_);
lean_inc(v___x_1958_);
v___x_1959_ = lean_apply_7(v_m_1950_, v___x_1958_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, lean_box(0));
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1970_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_1970_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1970_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v_lemmas_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1964_ = lean_st_ref_get(v___x_1958_);
lean_dec(v___x_1958_);
v_lemmas_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc_ref(v_lemmas_1965_);
lean_dec(v___x_1964_);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_a_1960_);
lean_ctor_set(v___x_1966_, 1, v_lemmas_1965_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1966_);
v___x_1968_ = v___x_1962_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v___x_1958_);
v_a_1971_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1959_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1959_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg___boxed(lean_object* v_m_1979_, lean_object* v_state_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg(v_m_1979_, v_state_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run(lean_object* v_00_u03b1_1988_, lean_object* v_m_1989_, lean_object* v_state_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg(v_m_1989_, v_state_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_m_1999_, lean_object* v_state_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run(v_00_u03b1_1998_, v_m_1999_, v_state_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg(lean_object* v_lemma_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2011_; lean_object* v_lemmas_2012_; lean_object* v_bvExprCache_2013_; lean_object* v_bvPredCache_2014_; lean_object* v_bvLogicalCache_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2026_; 
v___x_2011_ = lean_st_ref_take(v_a_2009_);
v_lemmas_2012_ = lean_ctor_get(v___x_2011_, 0);
v_bvExprCache_2013_ = lean_ctor_get(v___x_2011_, 1);
v_bvPredCache_2014_ = lean_ctor_get(v___x_2011_, 2);
v_bvLogicalCache_2015_ = lean_ctor_get(v___x_2011_, 3);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2017_ = v___x_2011_;
v_isShared_2018_ = v_isSharedCheck_2026_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_bvLogicalCache_2015_);
lean_inc(v_bvPredCache_2014_);
lean_inc(v_bvExprCache_2013_);
lean_inc(v_lemmas_2012_);
lean_dec(v___x_2011_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2026_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_array_push(v_lemmas_2012_, v_lemma_2008_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_bvExprCache_2013_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_bvPredCache_2014_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_bvLogicalCache_2015_);
v___x_2021_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2022_ = lean_st_ref_set(v_a_2009_, v___x_2021_);
v___x_2023_ = lean_box(0);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
return v___x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg___boxed(lean_object* v_lemma_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg(v_lemma_2027_, v_a_2028_);
lean_dec(v_a_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma(lean_object* v_lemma_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg(v_lemma_2031_, v_a_2032_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___boxed(lean_object* v_lemma_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma(v_lemma_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec(v_a_2041_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache(lean_object* v_e_2051_, lean_object* v_f_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v___x_2060_; lean_object* v_bvExprCache_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2060_ = lean_st_ref_get(v_a_2053_);
v_bvExprCache_2061_ = lean_ctor_get(v___x_2060_, 1);
lean_inc_ref(v_bvExprCache_2061_);
lean_dec(v___x_2060_);
v___x_2062_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__0));
v___x_2063_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__1));
lean_inc_ref(v_e_2051_);
v___x_2064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_2062_, v___x_2063_, v_bvExprCache_2061_, v_e_2051_);
lean_dec_ref(v_bvExprCache_2061_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2065_; 
lean_inc(v_a_2058_);
lean_inc_ref(v_a_2057_);
lean_inc(v_a_2056_);
lean_inc_ref(v_a_2055_);
lean_inc(v_a_2054_);
lean_inc(v_a_2053_);
lean_inc_ref(v_e_2051_);
v___x_2065_ = lean_apply_8(v_f_2052_, v_e_2051_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, lean_box(0));
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2087_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2087_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2087_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v_lemmas_2071_; lean_object* v_bvExprCache_2072_; lean_object* v_bvPredCache_2073_; lean_object* v_bvLogicalCache_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2086_; 
v___x_2070_ = lean_st_ref_take(v_a_2053_);
v_lemmas_2071_ = lean_ctor_get(v___x_2070_, 0);
v_bvExprCache_2072_ = lean_ctor_get(v___x_2070_, 1);
v_bvPredCache_2073_ = lean_ctor_get(v___x_2070_, 2);
v_bvLogicalCache_2074_ = lean_ctor_get(v___x_2070_, 3);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2076_ = v___x_2070_;
v_isShared_2077_ = v_isSharedCheck_2086_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_bvLogicalCache_2074_);
lean_inc(v_bvPredCache_2073_);
lean_inc(v_bvExprCache_2072_);
lean_inc(v_lemmas_2071_);
lean_dec(v___x_2070_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2086_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
lean_inc(v_a_2066_);
v___x_2078_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2062_, v___x_2063_, v_bvExprCache_2072_, v_e_2051_, v_a_2066_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_lemmas_2071_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_bvPredCache_2073_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_bvLogicalCache_2074_);
v___x_2080_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_st_ref_set(v_a_2053_, v___x_2080_);
if (v_isShared_2069_ == 0)
{
v___x_2083_ = v___x_2068_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2066_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2051_);
return v___x_2065_;
}
}
else
{
lean_object* v_val_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_f_2052_);
lean_dec_ref(v_e_2051_);
v_val_2088_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2064_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_val_2088_);
lean_dec(v___x_2064_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set_tag(v___x_2090_, 0);
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_val_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___boxed(lean_object* v_e_2096_, lean_object* v_f_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache(v_e_2096_, v_f_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec(v_a_2098_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache(lean_object* v_e_2106_, lean_object* v_f_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v_bvPredCache_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2115_ = lean_st_ref_get(v_a_2108_);
v_bvPredCache_2116_ = lean_ctor_get(v___x_2115_, 2);
lean_inc_ref(v_bvPredCache_2116_);
lean_dec(v___x_2115_);
v___x_2117_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__0));
v___x_2118_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__1));
lean_inc_ref(v_e_2106_);
v___x_2119_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_2117_, v___x_2118_, v_bvPredCache_2116_, v_e_2106_);
lean_dec_ref(v_bvPredCache_2116_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2120_; 
lean_inc(v_a_2113_);
lean_inc_ref(v_a_2112_);
lean_inc(v_a_2111_);
lean_inc_ref(v_a_2110_);
lean_inc(v_a_2109_);
lean_inc(v_a_2108_);
lean_inc_ref(v_e_2106_);
v___x_2120_ = lean_apply_8(v_f_2107_, v_e_2106_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, lean_box(0));
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2142_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2142_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2142_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; lean_object* v_lemmas_2126_; lean_object* v_bvExprCache_2127_; lean_object* v_bvPredCache_2128_; lean_object* v_bvLogicalCache_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2141_; 
v___x_2125_ = lean_st_ref_take(v_a_2108_);
v_lemmas_2126_ = lean_ctor_get(v___x_2125_, 0);
v_bvExprCache_2127_ = lean_ctor_get(v___x_2125_, 1);
v_bvPredCache_2128_ = lean_ctor_get(v___x_2125_, 2);
v_bvLogicalCache_2129_ = lean_ctor_get(v___x_2125_, 3);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2131_ = v___x_2125_;
v_isShared_2132_ = v_isSharedCheck_2141_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_bvLogicalCache_2129_);
lean_inc(v_bvPredCache_2128_);
lean_inc(v_bvExprCache_2127_);
lean_inc(v_lemmas_2126_);
lean_dec(v___x_2125_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2141_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
lean_inc(v_a_2121_);
v___x_2133_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2117_, v___x_2118_, v_bvPredCache_2128_, v_e_2106_, v_a_2121_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 2, v___x_2133_);
v___x_2135_ = v___x_2131_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_lemmas_2126_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_bvExprCache_2127_);
lean_ctor_set(v_reuseFailAlloc_2140_, 2, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2140_, 3, v_bvLogicalCache_2129_);
v___x_2135_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = lean_st_ref_set(v_a_2108_, v___x_2135_);
if (v_isShared_2124_ == 0)
{
v___x_2138_ = v___x_2123_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2121_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2106_);
return v___x_2120_;
}
}
else
{
lean_object* v_val_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec_ref(v_f_2107_);
lean_dec_ref(v_e_2106_);
v_val_2143_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2119_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_val_2143_);
lean_dec(v___x_2119_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set_tag(v___x_2145_, 0);
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_val_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___boxed(lean_object* v_e_2151_, lean_object* v_f_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache(v_e_2151_, v_f_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec(v_a_2153_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache(lean_object* v_e_2161_, lean_object* v_f_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2170_; lean_object* v_bvLogicalCache_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2170_ = lean_st_ref_get(v_a_2163_);
v_bvLogicalCache_2171_ = lean_ctor_get(v___x_2170_, 3);
lean_inc_ref(v_bvLogicalCache_2171_);
lean_dec(v___x_2170_);
v___x_2172_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__0));
v___x_2173_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__1));
lean_inc_ref(v_e_2161_);
v___x_2174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_2172_, v___x_2173_, v_bvLogicalCache_2171_, v_e_2161_);
lean_dec_ref(v_bvLogicalCache_2171_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v___x_2175_; 
lean_inc(v_a_2168_);
lean_inc_ref(v_a_2167_);
lean_inc(v_a_2166_);
lean_inc_ref(v_a_2165_);
lean_inc(v_a_2164_);
lean_inc(v_a_2163_);
lean_inc_ref(v_e_2161_);
v___x_2175_ = lean_apply_8(v_f_2162_, v_e_2161_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, lean_box(0));
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2197_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2197_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2197_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v_lemmas_2181_; lean_object* v_bvExprCache_2182_; lean_object* v_bvPredCache_2183_; lean_object* v_bvLogicalCache_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2196_; 
v___x_2180_ = lean_st_ref_take(v_a_2163_);
v_lemmas_2181_ = lean_ctor_get(v___x_2180_, 0);
v_bvExprCache_2182_ = lean_ctor_get(v___x_2180_, 1);
v_bvPredCache_2183_ = lean_ctor_get(v___x_2180_, 2);
v_bvLogicalCache_2184_ = lean_ctor_get(v___x_2180_, 3);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2186_ = v___x_2180_;
v_isShared_2187_ = v_isSharedCheck_2196_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_bvLogicalCache_2184_);
lean_inc(v_bvPredCache_2183_);
lean_inc(v_bvExprCache_2182_);
lean_inc(v_lemmas_2181_);
lean_dec(v___x_2180_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2196_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2190_; 
lean_inc(v_a_2176_);
v___x_2188_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2172_, v___x_2173_, v_bvLogicalCache_2184_, v_e_2161_, v_a_2176_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 3, v___x_2188_);
v___x_2190_ = v___x_2186_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_lemmas_2181_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_bvExprCache_2182_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_bvPredCache_2183_);
lean_ctor_set(v_reuseFailAlloc_2195_, 3, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2191_ = lean_st_ref_set(v_a_2163_, v___x_2190_);
if (v_isShared_2179_ == 0)
{
v___x_2193_ = v___x_2178_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2176_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2161_);
return v___x_2175_;
}
}
else
{
lean_object* v_val_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref(v_f_2162_);
lean_dec_ref(v_e_2161_);
v_val_2198_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2174_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_val_2198_);
lean_dec(v___x_2174_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set_tag(v___x_2200_, 0);
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_val_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___boxed(lean_object* v_e_2206_, lean_object* v_f_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache(v_e_2206_, v_f_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec(v_a_2208_);
return v_res_2215_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp);
l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVUnOp);
l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinPred);
l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprGate);
l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect(builtin);
}
#ifdef __cplusplus
}
#endif
