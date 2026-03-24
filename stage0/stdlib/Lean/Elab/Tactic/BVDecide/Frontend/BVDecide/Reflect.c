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
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__0;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "New atom of width "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", synthetic\? "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__8;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.Reflect"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Elab.Tactic.BVDecide.Frontend.M.lookup"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "The same atom occurs with different widths, this is a bug"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_w_342_);
v_start_343_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_start_343_);
v_expr_344_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_expr_344_);
lean_dec_ref(v_a_329_);
v___x_345_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__13);
lean_inc(v_w_342_);
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
lean_inc(v_w_328_);
v___x_355_ = l_Lean_mkNatLit(v_w_328_);
lean_inc(v_w_328_);
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
lean_inc(v_l_392_);
v_r_393_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_r_393_);
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
lean_inc(v_l_392_);
v___x_401_ = l_Lean_mkNatLit(v_l_392_);
lean_inc(v_r_393_);
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
lean_inc(v_w_406_);
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
lean_inc(v_w_406_);
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
lean_inc(v_n_418_);
v_lhs_419_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_lhs_419_);
v_rhs_420_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_rhs_420_);
lean_dec_ref(v_a_329_);
v___x_421_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__37, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__37_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__37);
lean_inc(v_w_328_);
v___x_422_ = l_Lean_mkNatLit(v_w_328_);
lean_inc(v_n_418_);
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
lean_inc(v_n_427_);
v_lhs_428_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_lhs_428_);
v_rhs_429_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_rhs_429_);
lean_dec_ref(v_a_329_);
v___x_430_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__40, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__40_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__40);
lean_inc(v_w_328_);
v___x_431_ = l_Lean_mkNatLit(v_w_328_);
lean_inc(v_n_427_);
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
lean_inc(v_n_436_);
v_lhs_437_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_lhs_437_);
v_rhs_438_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_rhs_438_);
lean_dec_ref(v_a_329_);
v___x_439_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__43, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__43_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVExpr_go___closed__43);
lean_inc(v_w_328_);
v___x_440_ = l_Lean_mkNatLit(v_w_328_);
lean_inc(v_n_436_);
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
lean_inc(v_w_582_);
v_lhs_583_ = lean_ctor_get(v_a_581_, 1);
lean_inc_ref(v_lhs_583_);
v_op_584_ = lean_ctor_get_uint8(v_a_581_, sizeof(void*)*3);
v_rhs_585_ = lean_ctor_get(v_a_581_, 2);
lean_inc_ref(v_rhs_585_);
lean_dec_ref(v_a_581_);
v___x_586_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__2);
lean_inc(v_w_582_);
v___x_587_ = l_Lean_mkNatLit(v_w_582_);
lean_inc(v_w_582_);
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
v___x_592_ = l_Lean_mkApp4(v___x_586_, v___x_587_, v___x_588_, v___y_590_, v___x_591_);
return v___x_592_;
}
}
else
{
lean_object* v_w_595_; lean_object* v_expr_596_; lean_object* v_idx_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_w_595_ = lean_ctor_get(v_a_581_, 0);
lean_inc(v_w_595_);
v_expr_596_ = lean_ctor_get(v_a_581_, 1);
lean_inc_ref(v_expr_596_);
v_idx_597_ = lean_ctor_get(v_a_581_, 2);
lean_inc(v_idx_597_);
lean_dec_ref(v_a_581_);
v___x_598_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBVPred_go___closed__5);
lean_inc(v_w_595_);
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
lean_inc_ref(v_inst_680_);
v___x_719_ = l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_714_);
lean_inc_ref(v_inst_680_);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0(lean_object* v_x1_1180_, lean_object* v_x2_1181_){
_start:
{
lean_object* v_snd_1182_; lean_object* v_snd_1183_; lean_object* v_atomNumber_1184_; lean_object* v_atomNumber_1185_; uint8_t v___x_1186_; 
v_snd_1182_ = lean_ctor_get(v_x1_1180_, 1);
v_snd_1183_ = lean_ctor_get(v_x2_1181_, 1);
v_atomNumber_1184_ = lean_ctor_get(v_snd_1182_, 1);
v_atomNumber_1185_ = lean_ctor_get(v_snd_1183_, 1);
v___x_1186_ = lean_nat_dec_lt(v_atomNumber_1184_, v_atomNumber_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0___boxed(lean_object* v_x1_1187_, lean_object* v_x2_1188_){
_start:
{
uint8_t v_res_1189_; lean_object* v_r_1190_; 
v_res_1189_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___lam__0(v_x1_1187_, v_x2_1188_);
lean_dec_ref(v_x2_1188_);
lean_dec_ref(v_x1_1187_);
v_r_1190_ = lean_box(v_res_1189_);
return v_r_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(lean_object* v_as_1192_, lean_object* v_lo_1193_, lean_object* v_hi_1194_){
_start:
{
uint8_t v___x_1195_; 
v___x_1195_ = lean_nat_dec_lt(v_lo_1193_, v_hi_1194_);
if (v___x_1195_ == 0)
{
lean_dec(v_lo_1193_);
return v_as_1192_;
}
else
{
lean_object* v___f_1196_; lean_object* v___x_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; uint8_t v___x_1200_; 
v___f_1196_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___closed__0));
lean_inc(v_lo_1193_);
v___x_1197_ = l_Array_qpartition___redArg(v_as_1192_, v___f_1196_, v_lo_1193_, v_hi_1194_);
v_fst_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_fst_1198_);
v_snd_1199_ = lean_ctor_get(v___x_1197_, 1);
lean_inc(v_snd_1199_);
lean_dec_ref(v___x_1197_);
v___x_1200_ = lean_nat_dec_le(v_hi_1194_, v_fst_1198_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(v_snd_1199_, v_lo_1193_, v_fst_1198_);
v___x_1202_ = lean_unsigned_to_nat(1u);
v___x_1203_ = lean_nat_add(v_fst_1198_, v___x_1202_);
lean_dec(v_fst_1198_);
v_as_1192_ = v___x_1201_;
v_lo_1193_ = v___x_1203_;
goto _start;
}
else
{
lean_dec(v_fst_1198_);
lean_dec(v_lo_1193_);
return v_snd_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg___boxed(lean_object* v_as_1205_, lean_object* v_lo_1206_, lean_object* v_hi_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(v_as_1205_, v_lo_1206_, v_hi_1207_);
lean_dec(v_hi_1207_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0(size_t v_sz_1209_, size_t v_i_1210_, lean_object* v_bs_1211_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_usize_dec_lt(v_i_1210_, v_sz_1209_);
if (v___x_1212_ == 0)
{
return v_bs_1211_;
}
else
{
lean_object* v_v_1213_; lean_object* v_snd_1214_; lean_object* v_fst_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1229_; 
v_v_1213_ = lean_array_uget(v_bs_1211_, v_i_1210_);
v_snd_1214_ = lean_ctor_get(v_v_1213_, 1);
v_fst_1215_ = lean_ctor_get(v_v_1213_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_v_1213_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1217_ = v_v_1213_;
v_isShared_1218_ = v_isSharedCheck_1229_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_snd_1214_);
lean_inc(v_fst_1215_);
lean_dec(v_v_1213_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1229_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_width_1219_; lean_object* v___x_1220_; lean_object* v_bs_x27_1221_; lean_object* v___x_1223_; 
v_width_1219_ = lean_ctor_get(v_snd_1214_, 0);
lean_inc(v_width_1219_);
lean_dec(v_snd_1214_);
v___x_1220_ = lean_unsigned_to_nat(0u);
v_bs_x27_1221_ = lean_array_uset(v_bs_1211_, v_i_1210_, v___x_1220_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v_fst_1215_);
lean_ctor_set(v___x_1217_, 0, v_width_1219_);
v___x_1223_ = v___x_1217_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_width_1219_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_fst_1215_);
v___x_1223_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
size_t v___x_1224_; size_t v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = ((size_t)1ULL);
v___x_1225_ = lean_usize_add(v_i_1210_, v___x_1224_);
v___x_1226_ = lean_array_uset(v_bs_x27_1221_, v_i_1210_, v___x_1223_);
v_i_1210_ = v___x_1225_;
v_bs_1211_ = v___x_1226_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0___boxed(lean_object* v_sz_1230_, lean_object* v_i_1231_, lean_object* v_bs_1232_){
_start:
{
size_t v_sz_boxed_1233_; size_t v_i_boxed_1234_; lean_object* v_res_1235_; 
v_sz_boxed_1233_ = lean_unbox_usize(v_sz_1230_);
lean_dec(v_sz_1230_);
v_i_boxed_1234_ = lean_unbox_usize(v_i_1231_);
lean_dec(v_i_1231_);
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0(v_sz_boxed_1233_, v_i_boxed_1234_, v_bs_1232_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg(lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1238_; lean_object* v___y_1240_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1258_; lean_object* v_atoms_1265_; lean_object* v_size_1266_; lean_object* v_buckets_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1238_ = lean_st_ref_get(v_a_1236_);
v_atoms_1265_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_ref(v_atoms_1265_);
lean_dec(v___x_1238_);
v_size_1266_ = lean_ctor_get(v_atoms_1265_, 0);
lean_inc(v_size_1266_);
v_buckets_1267_ = lean_ctor_get(v_atoms_1265_, 1);
lean_inc_ref(v_buckets_1267_);
lean_dec_ref(v_atoms_1265_);
v___x_1268_ = lean_mk_empty_array_with_capacity(v_size_1266_);
lean_dec(v_size_1266_);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_array_get_size(v_buckets_1267_);
v___x_1271_ = lean_nat_dec_lt(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_dec_ref(v_buckets_1267_);
v___y_1258_ = v___x_1268_;
goto v___jp_1257_;
}
else
{
uint8_t v___x_1272_; 
v___x_1272_ = lean_nat_dec_le(v___x_1270_, v___x_1270_);
if (v___x_1272_ == 0)
{
if (v___x_1271_ == 0)
{
lean_dec_ref(v_buckets_1267_);
v___y_1258_ = v___x_1268_;
goto v___jp_1257_;
}
else
{
size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = lean_usize_of_nat(v___x_1270_);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__3(v_buckets_1267_, v___x_1273_, v___x_1274_, v___x_1268_);
lean_dec_ref(v_buckets_1267_);
v___y_1258_ = v___x_1275_;
goto v___jp_1257_;
}
}
else
{
size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = ((size_t)0ULL);
v___x_1277_ = lean_usize_of_nat(v___x_1270_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__3(v_buckets_1267_, v___x_1276_, v___x_1277_, v___x_1268_);
lean_dec_ref(v_buckets_1267_);
v___y_1258_ = v___x_1278_;
goto v___jp_1257_;
}
}
v___jp_1239_:
{
size_t v_sz_1241_; size_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_sz_1241_ = lean_array_size(v___y_1240_);
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__0(v_sz_1241_, v___x_1242_, v___y_1240_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
v___jp_1245_:
{
lean_object* v___x_1250_; 
lean_dec(v___y_1248_);
v___x_1250_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(v___y_1247_, v___y_1246_, v___y_1249_);
lean_dec(v___y_1249_);
v___y_1240_ = v___x_1250_;
goto v___jp_1239_;
}
v___jp_1251_:
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_nat_dec_le(v___y_1255_, v___y_1252_);
if (v___x_1256_ == 0)
{
lean_dec(v___y_1252_);
lean_inc(v___y_1255_);
v___y_1246_ = v___y_1255_;
v___y_1247_ = v___y_1253_;
v___y_1248_ = v___y_1254_;
v___y_1249_ = v___y_1255_;
goto v___jp_1245_;
}
else
{
v___y_1246_ = v___y_1255_;
v___y_1247_ = v___y_1253_;
v___y_1248_ = v___y_1254_;
v___y_1249_ = v___y_1252_;
goto v___jp_1245_;
}
}
v___jp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = lean_array_get_size(v___y_1258_);
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = lean_nat_dec_eq(v___x_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_sub(v___x_1259_, v___x_1262_);
v___x_1264_ = lean_nat_dec_le(v___x_1260_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_inc(v___x_1263_);
v___y_1252_ = v___x_1263_;
v___y_1253_ = v___y_1258_;
v___y_1254_ = v___x_1259_;
v___y_1255_ = v___x_1263_;
goto v___jp_1251_;
}
else
{
v___y_1252_ = v___x_1263_;
v___y_1253_ = v___y_1258_;
v___y_1254_ = v___x_1259_;
v___y_1255_ = v___x_1260_;
goto v___jp_1251_;
}
}
else
{
v___y_1240_ = v___y_1258_;
goto v___jp_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg___boxed(lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg(v_a_1279_);
lean_dec(v_a_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms(lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg(v_a_1282_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___boxed(lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms(v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1(lean_object* v_n_1296_, lean_object* v_as_1297_, lean_object* v_lo_1298_, lean_object* v_hi_1299_, lean_object* v_w_1300_, lean_object* v_hlo_1301_, lean_object* v_hhi_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___redArg(v_as_1297_, v_lo_1298_, v_hi_1299_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1___boxed(lean_object* v_n_1304_, lean_object* v_as_1305_, lean_object* v_lo_1306_, lean_object* v_hi_1307_, lean_object* v_w_1308_, lean_object* v_hlo_1309_, lean_object* v_hhi_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_atoms_spec__1(v_n_1304_, v_as_1305_, v_lo_1306_, v_hi_1307_, v_w_1308_, v_hlo_1309_, v_hhi_1310_);
lean_dec(v_hi_1307_);
lean_dec(v_n_1304_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___lam__0(lean_object* v___x_1313_, lean_object* v___x_1314_, lean_object* v___x_1315_, lean_object* v___x_1316_, lean_object* v___x_1317_, lean_object* v___x_1318_, lean_object* v_x_1319_){
_start:
{
lean_object* v_fst_1320_; lean_object* v_snd_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_fst_1320_ = lean_ctor_get(v_x_1319_, 0);
lean_inc(v_fst_1320_);
v_snd_1321_ = lean_ctor_get(v_x_1319_, 1);
lean_inc(v_snd_1321_);
lean_dec_ref(v_x_1319_);
v___x_1322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0));
v___x_1323_ = l_Lean_Name_mkStr6(v___x_1313_, v___x_1314_, v___x_1315_, v___x_1316_, v___x_1317_, v___x_1322_);
v___x_1324_ = l_Lean_mkConst(v___x_1323_, v___x_1318_);
v___x_1325_ = l_Lean_mkNatLit(v_fst_1320_);
v___x_1326_ = l_Lean_mkAppB(v___x_1324_, v___x_1325_, v_snd_1321_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(lean_object* v_msgData_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; lean_object* v_env_1334_; lean_object* v___x_1335_; lean_object* v_mctx_1336_; lean_object* v_lctx_1337_; lean_object* v_options_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1333_ = lean_st_ref_get(v___y_1331_);
v_env_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc_ref(v_env_1334_);
lean_dec(v___x_1333_);
v___x_1335_ = lean_st_ref_get(v___y_1329_);
v_mctx_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc_ref(v_mctx_1336_);
lean_dec(v___x_1335_);
v_lctx_1337_ = lean_ctor_get(v___y_1328_, 2);
v_options_1338_ = lean_ctor_get(v___y_1330_, 2);
lean_inc_ref(v_options_1338_);
lean_inc_ref(v_lctx_1337_);
v___x_1339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1339_, 0, v_env_1334_);
lean_ctor_set(v___x_1339_, 1, v_mctx_1336_);
lean_ctor_set(v___x_1339_, 2, v_lctx_1337_);
lean_ctor_set(v___x_1339_, 3, v_options_1338_);
v___x_1340_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v_msgData_1327_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0___boxed(lean_object* v_msgData_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msgData_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(lean_object* v_msg_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_ref_1355_; lean_object* v___x_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1365_; 
v_ref_1355_ = lean_ctor_get(v___y_1352_, 5);
v___x_1356_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msg_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_inc(v_ref_1355_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_ref_1355_);
lean_ctor_set(v___x_1361_, 1, v_a_1357_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 1);
lean_ctor_set(v___x_1359_, 0, v___x_1361_);
v___x_1363_ = v___x_1359_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg___boxed(lean_object* v_msg_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v_msg_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1372_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__1(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__0));
v___x_1375_ = l_Lean_stringToMessageData(v___x_1374_);
return v___x_1375_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__5(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__3));
v___x_1392_ = l_Lean_mkConst(v___x_1391_, v___x_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment(lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___x_1399_; lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1436_; 
v___x_1399_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atoms___redArg(v_a_1393_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1436_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1436_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_array_get_size(v_a_1400_);
v___x_1406_ = lean_nat_dec_lt(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_del_object(v___x_1402_);
lean_dec(v_a_1400_);
v___x_1407_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__1);
v___x_1408_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v___x_1407_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v___x_1408_;
}
else
{
lean_object* v___x_1409_; lean_object* v___f_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = l_Lean_RArray_ofArray___redArg(v_a_1400_);
v___f_1410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__4));
v___x_1411_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__5, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__5_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___closed__5);
v___x_1412_ = l_Lean_RArray_toExpr___redArg(v___x_1411_, v___f_1410_, v___x_1409_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1435_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1435_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1435_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v_atoms_1418_; lean_object* v_evalsAtCache_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1433_; 
v___x_1417_ = lean_st_ref_take(v_a_1393_);
v_atoms_1418_ = lean_ctor_get(v___x_1417_, 0);
v_evalsAtCache_1419_ = lean_ctor_get(v___x_1417_, 2);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v___x_1417_, 1);
lean_dec(v_unused_1434_);
v___x_1421_ = v___x_1417_;
v_isShared_1422_ = v_isSharedCheck_1433_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_evalsAtCache_1419_);
lean_inc(v_atoms_1418_);
lean_dec(v___x_1417_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1433_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
lean_inc(v_a_1413_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 1);
lean_ctor_set(v___x_1402_, 0, v_a_1413_);
v___x_1424_ = v___x_1402_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1413_);
v___x_1424_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1426_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v___x_1424_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_atoms_1418_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_evalsAtCache_1419_);
v___x_1426_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = lean_st_ref_set(v_a_1393_, v___x_1426_);
if (v_isShared_1416_ == 0)
{
v___x_1429_ = v___x_1415_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1413_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1402_);
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment___boxed(lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment(v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0(lean_object* v_00_u03b1_1444_, lean_object* v_msg_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v_msg_1445_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___boxed(lean_object* v_00_u03b1_1453_, lean_object* v_msg_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0(v_00_u03b1_1453_, v_msg_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment(lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v_atomsAssignmentCache_1469_; 
v___x_1468_ = lean_st_ref_get(v_a_1462_);
v_atomsAssignmentCache_1469_ = lean_ctor_get(v___x_1468_, 1);
lean_inc(v_atomsAssignmentCache_1469_);
lean_dec(v___x_1468_);
if (lean_obj_tag(v_atomsAssignmentCache_1469_) == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment(v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
return v___x_1470_;
}
else
{
lean_object* v_val_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_val_1471_ = lean_ctor_get(v_atomsAssignmentCache_1469_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_atomsAssignmentCache_1469_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v_atomsAssignmentCache_1469_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_val_1471_);
lean_dec(v_atomsAssignmentCache_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set_tag(v___x_1473_, 0);
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_val_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment___boxed(lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment(v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(lean_object* v_cls_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_options_1492_; uint8_t v_hasTrace_1493_; 
v_options_1492_ = lean_ctor_get(v___y_1490_, 2);
v_hasTrace_1493_ = lean_ctor_get_uint8(v_options_1492_, sizeof(void*)*1);
if (v_hasTrace_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec(v_cls_1489_);
v___x_1494_ = lean_box(v_hasTrace_1493_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
return v___x_1495_;
}
else
{
lean_object* v_inheritedTraceOptions_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v_inheritedTraceOptions_1496_ = lean_ctor_get(v___y_1490_, 13);
v___x_1497_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___closed__1));
v___x_1498_ = l_Lean_Name_append(v___x_1497_, v_cls_1489_);
v___x_1499_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1496_, v_options_1492_, v___x_1498_);
lean_dec(v___x_1498_);
v___x_1500_ = lean_box(v___x_1499_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg___boxed(lean_object* v_cls_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(v_cls_1502_, v___y_1503_);
lean_dec_ref(v___y_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0(lean_object* v_cls_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(v_cls_1506_, v___y_1510_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___boxed(lean_object* v_cls_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0(v_cls_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
return v_res_1521_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_instMonadEIO(lean_box(0));
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2(lean_object* v_msg_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v_toApplicative_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1598_; 
v___x_1534_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__0, &l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__0);
v___x_1535_ = l_StateRefT_x27_instMonad___redArg(v___x_1534_);
v_toApplicative_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v___x_1535_, 1);
lean_dec(v_unused_1599_);
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1598_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_toApplicative_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1598_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v_toFunctor_1540_; lean_object* v_toSeq_1541_; lean_object* v_toSeqLeft_1542_; lean_object* v_toSeqRight_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1596_; 
v_toFunctor_1540_ = lean_ctor_get(v_toApplicative_1536_, 0);
v_toSeq_1541_ = lean_ctor_get(v_toApplicative_1536_, 2);
v_toSeqLeft_1542_ = lean_ctor_get(v_toApplicative_1536_, 3);
v_toSeqRight_1543_ = lean_ctor_get(v_toApplicative_1536_, 4);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_toApplicative_1536_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v_toApplicative_1536_, 1);
lean_dec(v_unused_1597_);
v___x_1545_ = v_toApplicative_1536_;
v_isShared_1546_ = v_isSharedCheck_1596_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_toSeqRight_1543_);
lean_inc(v_toSeqLeft_1542_);
lean_inc(v_toSeq_1541_);
lean_inc(v_toFunctor_1540_);
lean_dec(v_toApplicative_1536_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1596_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___f_1547_; lean_object* v___f_1548_; lean_object* v___f_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___f_1554_; lean_object* v___x_1556_; 
v___f_1547_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__1));
v___f_1548_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__2));
lean_inc_ref(v_toFunctor_1540_);
v___f_1549_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1549_, 0, v_toFunctor_1540_);
v___f_1550_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1550_, 0, v_toFunctor_1540_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___f_1549_);
lean_ctor_set(v___x_1551_, 1, v___f_1550_);
v___f_1552_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1552_, 0, v_toSeqRight_1543_);
v___f_1553_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1553_, 0, v_toSeqLeft_1542_);
v___f_1554_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1554_, 0, v_toSeq_1541_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 4, v___f_1552_);
lean_ctor_set(v___x_1545_, 3, v___f_1553_);
lean_ctor_set(v___x_1545_, 2, v___f_1554_);
lean_ctor_set(v___x_1545_, 1, v___f_1547_);
lean_ctor_set(v___x_1545_, 0, v___x_1551_);
v___x_1556_ = v___x_1545_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___f_1547_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v___f_1554_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v___f_1553_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v___f_1552_);
v___x_1556_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1558_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 1, v___f_1548_);
lean_ctor_set(v___x_1538_, 0, v___x_1556_);
v___x_1558_ = v___x_1538_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___f_1548_);
v___x_1558_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; lean_object* v_toApplicative_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1592_; 
v___x_1559_ = l_StateRefT_x27_instMonad___redArg(v___x_1558_);
v_toApplicative_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v___x_1559_, 1);
lean_dec(v_unused_1593_);
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1592_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_toApplicative_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1592_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_toFunctor_1564_; lean_object* v_toSeq_1565_; lean_object* v_toSeqLeft_1566_; lean_object* v_toSeqRight_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1590_; 
v_toFunctor_1564_ = lean_ctor_get(v_toApplicative_1560_, 0);
v_toSeq_1565_ = lean_ctor_get(v_toApplicative_1560_, 2);
v_toSeqLeft_1566_ = lean_ctor_get(v_toApplicative_1560_, 3);
v_toSeqRight_1567_ = lean_ctor_get(v_toApplicative_1560_, 4);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_toApplicative_1560_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v_toApplicative_1560_, 1);
lean_dec(v_unused_1591_);
v___x_1569_ = v_toApplicative_1560_;
v_isShared_1570_ = v_isSharedCheck_1590_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_toSeqRight_1567_);
lean_inc(v_toSeqLeft_1566_);
lean_inc(v_toSeq_1565_);
lean_inc(v_toFunctor_1564_);
lean_dec(v_toApplicative_1560_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1590_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___f_1571_; lean_object* v___f_1572_; lean_object* v___f_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___f_1576_; lean_object* v___f_1577_; lean_object* v___f_1578_; lean_object* v___x_1580_; 
v___f_1571_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__3));
v___f_1572_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___closed__4));
lean_inc_ref(v_toFunctor_1564_);
v___f_1573_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1573_, 0, v_toFunctor_1564_);
v___f_1574_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1574_, 0, v_toFunctor_1564_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___f_1573_);
lean_ctor_set(v___x_1575_, 1, v___f_1574_);
v___f_1576_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1576_, 0, v_toSeqRight_1567_);
v___f_1577_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1577_, 0, v_toSeqLeft_1566_);
v___f_1578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1578_, 0, v_toSeq_1565_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 4, v___f_1576_);
lean_ctor_set(v___x_1569_, 3, v___f_1577_);
lean_ctor_set(v___x_1569_, 2, v___f_1578_);
lean_ctor_set(v___x_1569_, 1, v___f_1571_);
lean_ctor_set(v___x_1569_, 0, v___x_1575_);
v___x_1580_ = v___x_1569_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___f_1571_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v___f_1578_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v___f_1577_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v___f_1576_);
v___x_1580_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v___f_1572_);
lean_ctor_set(v___x_1562_, 0, v___x_1580_);
v___x_1582_ = v___x_1562_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___f_1572_);
v___x_1582_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_4147__overap_1586_; lean_object* v___x_1587_; 
v___x_1583_ = l_StateRefT_x27_instMonad___redArg(v___x_1582_);
v___x_1584_ = lean_box(0);
v___x_1585_ = l_instInhabitedOfMonad___redArg(v___x_1583_, v___x_1584_);
v___x_4147__overap_1586_ = lean_panic_fn(v___x_1585_, v_msg_1527_);
lean_inc(v___y_1532_);
lean_inc_ref(v___y_1531_);
lean_inc(v___y_1530_);
lean_inc_ref(v___y_1529_);
lean_inc(v___y_1528_);
v___x_1587_ = lean_apply_6(v___x_4147__overap_1586_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, lean_box(0));
return v___x_1587_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2___boxed(lean_object* v_msg_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2(v_msg_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
return v_res_1607_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1608_; double v___x_1609_; 
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = lean_float_of_nat(v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg(lean_object* v_cls_1613_, lean_object* v_msg_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_ref_1620_; lean_object* v___x_1621_; lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1666_; 
v_ref_1620_ = lean_ctor_get(v___y_1617_, 5);
v___x_1621_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect_0__Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msg_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1666_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1666_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v_traceState_1627_; lean_object* v_env_1628_; lean_object* v_nextMacroScope_1629_; lean_object* v_ngen_1630_; lean_object* v_auxDeclNGen_1631_; lean_object* v_cache_1632_; lean_object* v_messages_1633_; lean_object* v_infoState_1634_; lean_object* v_snapshotTasks_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1665_; 
v___x_1626_ = lean_st_ref_take(v___y_1618_);
v_traceState_1627_ = lean_ctor_get(v___x_1626_, 4);
v_env_1628_ = lean_ctor_get(v___x_1626_, 0);
v_nextMacroScope_1629_ = lean_ctor_get(v___x_1626_, 1);
v_ngen_1630_ = lean_ctor_get(v___x_1626_, 2);
v_auxDeclNGen_1631_ = lean_ctor_get(v___x_1626_, 3);
v_cache_1632_ = lean_ctor_get(v___x_1626_, 5);
v_messages_1633_ = lean_ctor_get(v___x_1626_, 6);
v_infoState_1634_ = lean_ctor_get(v___x_1626_, 7);
v_snapshotTasks_1635_ = lean_ctor_get(v___x_1626_, 8);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1637_ = v___x_1626_;
v_isShared_1638_ = v_isSharedCheck_1665_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_snapshotTasks_1635_);
lean_inc(v_infoState_1634_);
lean_inc(v_messages_1633_);
lean_inc(v_cache_1632_);
lean_inc(v_traceState_1627_);
lean_inc(v_auxDeclNGen_1631_);
lean_inc(v_ngen_1630_);
lean_inc(v_nextMacroScope_1629_);
lean_inc(v_env_1628_);
lean_dec(v___x_1626_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1665_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
uint64_t v_tid_1639_; lean_object* v_traces_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1664_; 
v_tid_1639_ = lean_ctor_get_uint64(v_traceState_1627_, sizeof(void*)*1);
v_traces_1640_ = lean_ctor_get(v_traceState_1627_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_traceState_1627_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1642_ = v_traceState_1627_;
v_isShared_1643_ = v_isSharedCheck_1664_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_traces_1640_);
lean_dec(v_traceState_1627_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1664_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; double v___x_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__0);
v___x_1646_ = 0;
v___x_1647_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__1));
v___x_1648_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1648_, 0, v_cls_1613_);
lean_ctor_set(v___x_1648_, 1, v___x_1644_);
lean_ctor_set(v___x_1648_, 2, v___x_1647_);
lean_ctor_set_float(v___x_1648_, sizeof(void*)*3, v___x_1645_);
lean_ctor_set_float(v___x_1648_, sizeof(void*)*3 + 8, v___x_1645_);
lean_ctor_set_uint8(v___x_1648_, sizeof(void*)*3 + 16, v___x_1646_);
v___x_1649_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___closed__2));
v___x_1650_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v_a_1622_);
lean_ctor_set(v___x_1650_, 2, v___x_1649_);
lean_inc(v_ref_1620_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v_ref_1620_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = l_Lean_PersistentArray_push___redArg(v_traces_1640_, v___x_1651_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1652_);
v___x_1654_ = v___x_1642_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1652_);
lean_ctor_set_uint64(v_reuseFailAlloc_1663_, sizeof(void*)*1, v_tid_1639_);
v___x_1654_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v___x_1654_);
v___x_1656_ = v___x_1637_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_env_1628_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_nextMacroScope_1629_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_ngen_1630_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v_auxDeclNGen_1631_);
lean_ctor_set(v_reuseFailAlloc_1662_, 4, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1662_, 5, v_cache_1632_);
lean_ctor_set(v_reuseFailAlloc_1662_, 6, v_messages_1633_);
lean_ctor_set(v_reuseFailAlloc_1662_, 7, v_infoState_1634_);
lean_ctor_set(v_reuseFailAlloc_1662_, 8, v_snapshotTasks_1635_);
v___x_1656_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1657_ = lean_st_ref_set(v___y_1618_, v___x_1656_);
v___x_1658_ = lean_box(0);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1658_);
v___x_1660_ = v___x_1624_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg___boxed(lean_object* v_cls_1667_, lean_object* v_msg_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg(v_cls_1667_, v_msg_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
return v_res_1674_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__4(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__3));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__6(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__5));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__8(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__7));
v___x_1689_ = l_Lean_stringToMessageData(v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__12(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__11));
v___x_1694_ = lean_unsigned_to_nat(6u);
v___x_1695_ = lean_unsigned_to_nat(310u);
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__10));
v___x_1697_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__9));
v___x_1698_ = l_mkPanicMessageWithDecl(v___x_1697_, v___x_1696_, v___x_1695_, v___x_1694_, v___x_1693_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup(lean_object* v_e_1699_, lean_object* v_width_1700_, uint8_t v_synthetic_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___y_1709_; lean_object* v___x_1728_; lean_object* v_atoms_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_st_ref_get(v_a_1702_);
v_atoms_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_ref(v_atoms_1729_);
lean_dec(v___x_1728_);
v___x_1730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_atoms_1729_, v_e_1699_);
lean_dec_ref(v_atoms_1729_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1767_; 
v___x_1731_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__2));
v___x_1732_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(v___x_1731_, v_a_1705_);
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1767_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1767_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_unbox(v_a_1733_);
lean_dec(v_a_1733_);
if (v___x_1737_ == 0)
{
lean_del_object(v___x_1735_);
v___y_1709_ = v_a_1702_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1738_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__4);
lean_inc(v_width_1700_);
v___x_1739_ = l_Nat_reprFast(v_width_1700_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 3);
lean_ctor_set(v___x_1735_, 0, v___x_1739_);
v___x_1741_ = v___x_1735_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___y_1747_; 
v___x_1742_ = l_Lean_MessageData_ofFormat(v___x_1741_);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1738_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__6);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
if (v_synthetic_1701_ == 0)
{
lean_object* v___x_1764_; 
v___x_1764_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__7));
v___y_1747_ = v___x_1764_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1765_; 
v___x_1765_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprBoolExpr_go___redArg___closed__10));
v___y_1747_ = v___x_1765_;
goto v___jp_1746_;
}
v___jp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1748_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___y_1747_);
v___x_1749_ = l_Lean_MessageData_ofFormat(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1745_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__8);
v___x_1752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1750_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
lean_inc_ref(v_e_1699_);
v___x_1753_ = l_Lean_MessageData_ofExpr(v_e_1699_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg(v___x_1731_, v___x_1754_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_dec_ref(v___x_1755_);
v___y_1709_ = v_a_1702_;
goto v___jp_1708_;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_width_1700_);
lean_dec_ref(v_e_1699_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
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
lean_object* v_val_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v_e_1699_);
v_val_1768_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1770_ = v___x_1730_;
v_isShared_1771_ = v_isSharedCheck_1796_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_val_1768_);
lean_dec(v___x_1730_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1796_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_width_1772_; lean_object* v_atomNumber_1773_; uint8_t v___x_1774_; 
v_width_1772_ = lean_ctor_get(v_val_1768_, 0);
lean_inc(v_width_1772_);
v_atomNumber_1773_ = lean_ctor_get(v_val_1768_, 1);
lean_inc(v_atomNumber_1773_);
lean_dec(v_val_1768_);
v___x_1774_ = lean_nat_dec_eq(v_width_1700_, v_width_1772_);
lean_dec(v_width_1772_);
lean_dec(v_width_1700_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_del_object(v___x_1770_);
v___x_1775_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___closed__12);
v___x_1776_ = l_panic___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__2(v___x_1775_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v___x_1776_, 0);
lean_dec(v_unused_1784_);
v___x_1778_ = v___x_1776_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v___x_1776_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v_atomNumber_1773_);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_atomNumber_1773_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_atomNumber_1773_);
v_a_1785_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1776_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1776_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
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
else
{
lean_object* v___x_1794_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 0);
lean_ctor_set(v___x_1770_, 0, v_atomNumber_1773_);
v___x_1794_ = v___x_1770_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_atomNumber_1773_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
v___jp_1708_:
{
lean_object* v___x_1710_; lean_object* v_atoms_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1725_; 
v___x_1710_ = lean_st_ref_take(v___y_1709_);
v_atoms_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; lean_object* v_unused_1727_; 
v_unused_1726_ = lean_ctor_get(v___x_1710_, 2);
lean_dec(v_unused_1726_);
v_unused_1727_ = lean_ctor_get(v___x_1710_, 1);
lean_dec(v_unused_1727_);
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_atoms_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_size_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v_size_1715_ = lean_ctor_get(v_atoms_1711_, 0);
lean_inc(v_size_1715_);
lean_inc(v_size_1715_);
v___x_1716_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1716_, 0, v_width_1700_);
lean_ctor_set(v___x_1716_, 1, v_size_1715_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*2, v_synthetic_1701_);
v___x_1717_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_atoms_1711_, v_e_1699_, v___x_1716_);
v___x_1718_ = lean_box(0);
v___x_1719_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg___closed__1);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 2, v___x_1719_);
lean_ctor_set(v___x_1713_, 1, v___x_1718_);
lean_ctor_set(v___x_1713_, 0, v___x_1717_);
v___x_1721_ = v___x_1713_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_st_ref_set(v___y_1709_, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v_size_1715_);
return v___x_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup___boxed(lean_object* v_e_1797_, lean_object* v_width_1798_, lean_object* v_synthetic_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
uint8_t v_synthetic_boxed_1806_; lean_object* v_res_1807_; 
v_synthetic_boxed_1806_ = lean_unbox(v_synthetic_1799_);
v_res_1807_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup(v_e_1797_, v_width_1798_, v_synthetic_boxed_1806_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1(lean_object* v_cls_1808_, lean_object* v_msg_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg(v_cls_1808_, v_msg_1809_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___boxed(lean_object* v_cls_1817_, lean_object* v_msg_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1(v_cls_1817_, v_msg_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27(lean_object* v_mkFRefl_1826_, lean_object* v_fst_1827_, lean_object* v_fproof_1828_, lean_object* v_mkSRefl_1829_, lean_object* v_snd_1830_, lean_object* v_sproof_1831_){
_start:
{
if (lean_obj_tag(v_fproof_1828_) == 0)
{
lean_dec_ref(v_snd_1830_);
lean_dec_ref(v_mkSRefl_1829_);
if (lean_obj_tag(v_sproof_1831_) == 0)
{
lean_object* v___x_1832_; 
lean_dec_ref(v_fst_1827_);
lean_dec_ref(v_mkFRefl_1826_);
v___x_1832_ = lean_box(0);
return v___x_1832_;
}
else
{
lean_object* v_val_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1842_; 
v_val_1833_ = lean_ctor_get(v_sproof_1831_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_sproof_1831_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1835_ = v_sproof_1831_;
v_isShared_1836_ = v_isSharedCheck_1842_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_val_1833_);
lean_dec(v_sproof_1831_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1842_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1837_ = lean_apply_1(v_mkFRefl_1826_, v_fst_1827_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v_val_1833_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1838_);
v___x_1840_ = v___x_1835_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
else
{
lean_dec_ref(v_fst_1827_);
lean_dec_ref(v_mkFRefl_1826_);
if (lean_obj_tag(v_sproof_1831_) == 0)
{
lean_object* v_val_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1852_; 
v_val_1843_ = lean_ctor_get(v_fproof_1828_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_fproof_1828_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1845_ = v_fproof_1828_;
v_isShared_1846_ = v_isSharedCheck_1852_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_val_1843_);
lean_dec(v_fproof_1828_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1852_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1847_ = lean_apply_1(v_mkSRefl_1829_, v_snd_1830_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_val_1843_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1848_);
v___x_1850_ = v___x_1845_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
else
{
lean_object* v_val_1853_; lean_object* v_val_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v_snd_1830_);
lean_dec_ref(v_mkSRefl_1829_);
v_val_1853_ = lean_ctor_get(v_fproof_1828_, 0);
lean_inc(v_val_1853_);
lean_dec_ref(v_fproof_1828_);
v_val_1854_ = lean_ctor_get(v_sproof_1831_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_sproof_1831_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1856_ = v_sproof_1831_;
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_val_1854_);
lean_dec(v_sproof_1831_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_val_1853_);
lean_ctor_set(v___x_1858_, 1, v_val_1854_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1858_);
v___x_1860_ = v___x_1856_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof(lean_object* v_mkRefl_1863_, lean_object* v_fst_1864_, lean_object* v_fproof_1865_, lean_object* v_snd_1866_, lean_object* v_sproof_1867_){
_start:
{
lean_object* v___x_1868_; 
lean_inc_ref(v_mkRefl_1863_);
v___x_1868_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27(v_mkRefl_1863_, v_fst_1864_, v_fproof_1865_, v_mkRefl_1863_, v_snd_1866_, v_sproof_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyTernaryProof(lean_object* v_mkRefl_1869_, lean_object* v_fst_1870_, lean_object* v_fproof_1871_, lean_object* v_snd_1872_, lean_object* v_sproof_1873_, lean_object* v_thd_1874_, lean_object* v_tproof_1875_){
_start:
{
if (lean_obj_tag(v_fproof_1871_) == 0)
{
lean_object* v___x_1876_; 
lean_inc_ref_n(v_mkRefl_1869_, 2);
v___x_1876_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27(v_mkRefl_1869_, v_snd_1872_, v_sproof_1873_, v_mkRefl_1869_, v_thd_1874_, v_tproof_1875_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v___x_1877_; 
lean_dec_ref(v_fst_1870_);
lean_dec_ref(v_mkRefl_1869_);
v___x_1877_ = lean_box(0);
return v___x_1877_;
}
else
{
lean_object* v_val_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1887_; 
v_val_1878_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1880_ = v___x_1876_;
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_val_1878_);
lean_dec(v___x_1876_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1882_ = lean_apply_1(v_mkRefl_1869_, v_fst_1870_);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_val_1878_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1883_);
v___x_1885_ = v___x_1880_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_val_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v_fst_1870_);
v_val_1888_ = lean_ctor_get(v_fproof_1871_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_fproof_1871_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1890_ = v_fproof_1871_;
v_isShared_1891_ = v_isSharedCheck_1909_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_val_1888_);
lean_dec(v_fproof_1871_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1909_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; 
lean_inc_ref(v_thd_1874_);
lean_inc_ref(v_snd_1872_);
lean_inc_ref_n(v_mkRefl_1869_, 2);
v___x_1892_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27(v_mkRefl_1869_, v_snd_1872_, v_sproof_1873_, v_mkRefl_1869_, v_thd_1874_, v_tproof_1875_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
lean_inc_ref(v_mkRefl_1869_);
v___x_1893_ = lean_apply_1(v_mkRefl_1869_, v_snd_1872_);
v___x_1894_ = lean_apply_1(v_mkRefl_1869_, v_thd_1874_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_val_1888_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1896_);
v___x_1898_ = v___x_1890_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
else
{
lean_object* v_val_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1908_; 
lean_del_object(v___x_1890_);
lean_dec_ref(v_thd_1874_);
lean_dec_ref(v_snd_1872_);
lean_dec_ref(v_mkRefl_1869_);
v_val_1900_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1902_ = v___x_1892_;
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_val_1900_);
lean_dec(v___x_1892_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_val_1888_);
lean_ctor_set(v___x_1904_, 1, v_val_1900_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg(lean_object* v_m_1910_, lean_object* v_state_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_st_mk_ref(v_state_1911_);
lean_inc(v_a_1916_);
lean_inc_ref(v_a_1915_);
lean_inc(v_a_1914_);
lean_inc_ref(v_a_1913_);
lean_inc(v_a_1912_);
lean_inc(v___x_1918_);
v___x_1919_ = lean_apply_7(v_m_1910_, v___x_1918_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, lean_box(0));
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1930_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1930_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1930_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v_lemmas_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1924_ = lean_st_ref_get(v___x_1918_);
lean_dec(v___x_1918_);
v_lemmas_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc_ref(v_lemmas_1925_);
lean_dec(v___x_1924_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v_a_1920_);
lean_ctor_set(v___x_1926_, 1, v_lemmas_1925_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1926_);
v___x_1928_ = v___x_1922_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v___x_1918_);
v_a_1931_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1919_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1919_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg___boxed(lean_object* v_m_1939_, lean_object* v_state_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg(v_m_1939_, v_state_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run(lean_object* v_00_u03b1_1948_, lean_object* v_m_1949_, lean_object* v_state_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg(v_m_1949_, v_state_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___boxed(lean_object* v_00_u03b1_1958_, lean_object* v_m_1959_, lean_object* v_state_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run(v_00_u03b1_1958_, v_m_1959_, v_state_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg(lean_object* v_lemma_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v___x_1971_; lean_object* v_lemmas_1972_; lean_object* v_bvExprCache_1973_; lean_object* v_bvPredCache_1974_; lean_object* v_bvLogicalCache_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1986_; 
v___x_1971_ = lean_st_ref_take(v_a_1969_);
v_lemmas_1972_ = lean_ctor_get(v___x_1971_, 0);
v_bvExprCache_1973_ = lean_ctor_get(v___x_1971_, 1);
v_bvPredCache_1974_ = lean_ctor_get(v___x_1971_, 2);
v_bvLogicalCache_1975_ = lean_ctor_get(v___x_1971_, 3);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1977_ = v___x_1971_;
v_isShared_1978_ = v_isSharedCheck_1986_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_bvLogicalCache_1975_);
lean_inc(v_bvPredCache_1974_);
lean_inc(v_bvExprCache_1973_);
lean_inc(v_lemmas_1972_);
lean_dec(v___x_1971_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1986_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = lean_array_push(v_lemmas_1972_, v_lemma_1968_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1979_);
v___x_1981_ = v___x_1977_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_bvExprCache_1973_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_bvPredCache_1974_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v_bvLogicalCache_1975_);
v___x_1981_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = lean_st_ref_set(v_a_1969_, v___x_1981_);
v___x_1983_ = lean_box(0);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
return v___x_1984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg___boxed(lean_object* v_lemma_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg(v_lemma_1987_, v_a_1988_);
lean_dec(v_a_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma(lean_object* v_lemma_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___redArg(v_lemma_1991_, v_a_1992_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma___boxed(lean_object* v_lemma_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_addLemma(v_lemma_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec(v_a_2001_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache(lean_object* v_e_2011_, lean_object* v_f_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___x_2020_; lean_object* v_bvExprCache_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2020_ = lean_st_ref_get(v_a_2013_);
v_bvExprCache_2021_ = lean_ctor_get(v___x_2020_, 1);
lean_inc_ref(v_bvExprCache_2021_);
lean_dec(v___x_2020_);
v___x_2022_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__0));
v___x_2023_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__1));
lean_inc_ref(v_e_2011_);
v___x_2024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_2022_, v___x_2023_, v_bvExprCache_2021_, v_e_2011_);
lean_dec_ref(v_bvExprCache_2021_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v___x_2025_; 
lean_inc(v_a_2018_);
lean_inc_ref(v_a_2017_);
lean_inc(v_a_2016_);
lean_inc_ref(v_a_2015_);
lean_inc(v_a_2014_);
lean_inc(v_a_2013_);
lean_inc_ref(v_e_2011_);
v___x_2025_ = lean_apply_8(v_f_2012_, v_e_2011_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, lean_box(0));
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2047_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2047_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2047_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v_lemmas_2031_; lean_object* v_bvExprCache_2032_; lean_object* v_bvPredCache_2033_; lean_object* v_bvLogicalCache_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2046_; 
v___x_2030_ = lean_st_ref_take(v_a_2013_);
v_lemmas_2031_ = lean_ctor_get(v___x_2030_, 0);
v_bvExprCache_2032_ = lean_ctor_get(v___x_2030_, 1);
v_bvPredCache_2033_ = lean_ctor_get(v___x_2030_, 2);
v_bvLogicalCache_2034_ = lean_ctor_get(v___x_2030_, 3);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2036_ = v___x_2030_;
v_isShared_2037_ = v_isSharedCheck_2046_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_bvLogicalCache_2034_);
lean_inc(v_bvPredCache_2033_);
lean_inc(v_bvExprCache_2032_);
lean_inc(v_lemmas_2031_);
lean_dec(v___x_2030_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2046_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
lean_inc(v_a_2026_);
v___x_2038_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2022_, v___x_2023_, v_bvExprCache_2032_, v_e_2011_, v_a_2026_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v___x_2038_);
v___x_2040_ = v___x_2036_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_lemmas_2031_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_bvPredCache_2033_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_bvLogicalCache_2034_);
v___x_2040_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2041_ = lean_st_ref_set(v_a_2013_, v___x_2040_);
if (v_isShared_2029_ == 0)
{
v___x_2043_ = v___x_2028_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2026_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2011_);
return v___x_2025_;
}
}
else
{
lean_object* v_val_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v_f_2012_);
lean_dec_ref(v_e_2011_);
v_val_2048_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2024_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_val_2048_);
lean_dec(v___x_2024_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set_tag(v___x_2050_, 0);
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_val_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___boxed(lean_object* v_e_2056_, lean_object* v_f_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache(v_e_2056_, v_f_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_a_2059_);
lean_dec(v_a_2058_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache(lean_object* v_e_2066_, lean_object* v_f_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v___x_2075_; lean_object* v_bvPredCache_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2075_ = lean_st_ref_get(v_a_2068_);
v_bvPredCache_2076_ = lean_ctor_get(v___x_2075_, 2);
lean_inc_ref(v_bvPredCache_2076_);
lean_dec(v___x_2075_);
v___x_2077_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__0));
v___x_2078_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__1));
lean_inc_ref(v_e_2066_);
v___x_2079_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_2077_, v___x_2078_, v_bvPredCache_2076_, v_e_2066_);
lean_dec_ref(v_bvPredCache_2076_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v___x_2080_; 
lean_inc(v_a_2073_);
lean_inc_ref(v_a_2072_);
lean_inc(v_a_2071_);
lean_inc_ref(v_a_2070_);
lean_inc(v_a_2069_);
lean_inc(v_a_2068_);
lean_inc_ref(v_e_2066_);
v___x_2080_ = lean_apply_8(v_f_2067_, v_e_2066_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, lean_box(0));
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2102_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2102_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2102_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v_lemmas_2086_; lean_object* v_bvExprCache_2087_; lean_object* v_bvPredCache_2088_; lean_object* v_bvLogicalCache_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2101_; 
v___x_2085_ = lean_st_ref_take(v_a_2068_);
v_lemmas_2086_ = lean_ctor_get(v___x_2085_, 0);
v_bvExprCache_2087_ = lean_ctor_get(v___x_2085_, 1);
v_bvPredCache_2088_ = lean_ctor_get(v___x_2085_, 2);
v_bvLogicalCache_2089_ = lean_ctor_get(v___x_2085_, 3);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2091_ = v___x_2085_;
v_isShared_2092_ = v_isSharedCheck_2101_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_bvLogicalCache_2089_);
lean_inc(v_bvPredCache_2088_);
lean_inc(v_bvExprCache_2087_);
lean_inc(v_lemmas_2086_);
lean_dec(v___x_2085_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2101_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
lean_inc(v_a_2081_);
v___x_2093_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2077_, v___x_2078_, v_bvPredCache_2088_, v_e_2066_, v_a_2081_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 2, v___x_2093_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_lemmas_2086_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_bvExprCache_2087_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_bvLogicalCache_2089_);
v___x_2095_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = lean_st_ref_set(v_a_2068_, v___x_2095_);
if (v_isShared_2084_ == 0)
{
v___x_2098_ = v___x_2083_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2081_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2066_);
return v___x_2080_;
}
}
else
{
lean_object* v_val_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref(v_f_2067_);
lean_dec_ref(v_e_2066_);
v_val_2103_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2079_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_val_2103_);
lean_dec(v___x_2079_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 0);
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_val_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___boxed(lean_object* v_e_2111_, lean_object* v_f_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache(v_e_2111_, v_f_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec(v_a_2113_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache(lean_object* v_e_2121_, lean_object* v_f_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v_bvLogicalCache_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2130_ = lean_st_ref_get(v_a_2123_);
v_bvLogicalCache_2131_ = lean_ctor_get(v___x_2130_, 3);
lean_inc_ref(v_bvLogicalCache_2131_);
lean_dec(v___x_2130_);
v___x_2132_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__0));
v___x_2133_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___closed__1));
lean_inc_ref(v_e_2121_);
v___x_2134_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_2132_, v___x_2133_, v_bvLogicalCache_2131_, v_e_2121_);
lean_dec_ref(v_bvLogicalCache_2131_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v___x_2135_; 
lean_inc(v_a_2128_);
lean_inc_ref(v_a_2127_);
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc(v_a_2123_);
lean_inc_ref(v_e_2121_);
v___x_2135_ = lean_apply_8(v_f_2122_, v_e_2121_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, lean_box(0));
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2157_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2157_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2157_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v_lemmas_2141_; lean_object* v_bvExprCache_2142_; lean_object* v_bvPredCache_2143_; lean_object* v_bvLogicalCache_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2156_; 
v___x_2140_ = lean_st_ref_take(v_a_2123_);
v_lemmas_2141_ = lean_ctor_get(v___x_2140_, 0);
v_bvExprCache_2142_ = lean_ctor_get(v___x_2140_, 1);
v_bvPredCache_2143_ = lean_ctor_get(v___x_2140_, 2);
v_bvLogicalCache_2144_ = lean_ctor_get(v___x_2140_, 3);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2146_ = v___x_2140_;
v_isShared_2147_ = v_isSharedCheck_2156_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_bvLogicalCache_2144_);
lean_inc(v_bvPredCache_2143_);
lean_inc(v_bvExprCache_2142_);
lean_inc(v_lemmas_2141_);
lean_dec(v___x_2140_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2156_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_inc(v_a_2136_);
v___x_2148_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2132_, v___x_2133_, v_bvLogicalCache_2144_, v_e_2121_, v_a_2136_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 3, v___x_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_lemmas_2141_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_bvExprCache_2142_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_bvPredCache_2143_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = lean_st_ref_set(v_a_2123_, v___x_2150_);
if (v_isShared_2139_ == 0)
{
v___x_2153_ = v___x_2138_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2136_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2121_);
return v___x_2135_;
}
}
else
{
lean_object* v_val_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec_ref(v_f_2122_);
lean_dec_ref(v_e_2121_);
v_val_2158_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2134_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_val_2158_);
lean_dec(v___x_2134_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set_tag(v___x_2160_, 0);
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_val_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___boxed(lean_object* v_e_2166_, lean_object* v_f_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache(v_e_2166_, v_f_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec(v_a_2171_);
lean_dec_ref(v_a_2170_);
lean_dec(v_a_2169_);
lean_dec(v_a_2168_);
return v_res_2175_;
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
