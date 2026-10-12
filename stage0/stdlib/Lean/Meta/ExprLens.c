// Lean compiler output
// Module: Lean.Meta.ExprLens
// Imports: public import Lean.SubExpr
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_toArray(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Array_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Invalid coordinate "};
static const lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " for "};
static const lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lensing on types is not supported"};
static const lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Internal: Types should be handled by viewAux"};
static const lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Bad coordinate "};
static const lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Can't viewRaw the type of "};
static const lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewSubexpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewSubexpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lean_Core_viewBinders___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Core_viewBinders___redArg___closed__0 = (const lean_object*)&l_Lean_Core_viewBinders___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_numBinders___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_size___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Core_numBinders___redArg___closed__0 = (const lean_object*)&l_Lean_Core_numBinders___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Core_numBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_numBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(lean_object* v_body_1_, lean_object* v_g_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_expr_instantiate1(v_body_1_, v_x_3_);
v___x_5_ = lean_apply_1(v_g_2_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0___boxed(lean_object* v_body_6_, lean_object* v_g_7_, lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(v_body_6_, v_g_7_, v_x_8_);
lean_dec_ref(v_x_8_);
lean_dec_ref(v_body_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(lean_object* v_fn_10_, lean_object* v_toPure_11_, lean_object* v_arg_12_, lean_object* v_e_13_, lean_object* v_____do__lift_14_){
_start:
{
size_t v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_ptr_addr(v_fn_10_);
v___x_16_ = lean_usize_dec_eq(v___x_15_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec_ref(v_e_13_);
v___x_17_ = l_Lean_Expr_app___override(v_fn_10_, v_____do__lift_14_);
v___x_18_ = lean_apply_2(v_toPure_11_, lean_box(0), v___x_17_);
return v___x_18_;
}
else
{
size_t v___x_19_; size_t v___x_20_; uint8_t v___x_21_; 
v___x_19_ = lean_ptr_addr(v_arg_12_);
v___x_20_ = lean_ptr_addr(v_____do__lift_14_);
v___x_21_ = lean_usize_dec_eq(v___x_19_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec_ref(v_e_13_);
v___x_22_ = l_Lean_Expr_app___override(v_fn_10_, v_____do__lift_14_);
v___x_23_ = lean_apply_2(v_toPure_11_, lean_box(0), v___x_22_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
lean_dec_ref(v_____do__lift_14_);
lean_dec_ref(v_fn_10_);
v___x_24_ = lean_apply_2(v_toPure_11_, lean_box(0), v_e_13_);
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed(lean_object* v_fn_25_, lean_object* v_toPure_26_, lean_object* v_arg_27_, lean_object* v_e_28_, lean_object* v_____do__lift_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(v_fn_25_, v_toPure_26_, v_arg_27_, v_e_28_, v_____do__lift_29_);
lean_dec_ref(v_arg_27_);
return v_res_30_;
}
}
lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(lean_object* v___x_31_, uint8_t v___x_32_, uint8_t v___x_33_, lean_object* v_inst_34_, lean_object* v_____do__lift_35_){
_start:
{
uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_36_ = 1;
v___x_37_ = lean_box(v___x_32_);
v___x_38_ = lean_box(v___x_33_);
v___x_39_ = lean_box(v___x_32_);
v___x_40_ = lean_box(v___x_33_);
v___x_41_ = lean_box(v___x_36_);
v___x_42_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_42_, 0, v___x_31_);
lean_closure_set(v___x_42_, 1, v_____do__lift_35_);
lean_closure_set(v___x_42_, 2, v___x_37_);
lean_closure_set(v___x_42_, 3, v___x_38_);
lean_closure_set(v___x_42_, 4, v___x_39_);
lean_closure_set(v___x_42_, 5, v___x_40_);
lean_closure_set(v___x_42_, 6, v___x_41_);
v___x_43_ = lean_apply_2(v_inst_34_, lean_box(0), v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_31_ = stack[0].m_obj;
uint8_t v___x_32_ = stack[1].m_num;
uint8_t v___x_33_ = stack[2].m_num;
lean_object* v_inst_34_ = stack[3].m_obj;
lean_object* v_____do__lift_35_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(v___x_31_, v___x_32_, v___x_33_, v_inst_34_, v_____do__lift_35_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed(lean_object* v___x_45_, lean_object* v___x_46_, lean_object* v___x_47_, lean_object* v_inst_48_, lean_object* v_____do__lift_49_){
_start:
{
uint8_t v___x_1216__boxed_50_; uint8_t v___x_1217__boxed_51_; lean_object* v_res_52_; 
v___x_1216__boxed_50_ = lean_unbox(v___x_46_);
v___x_1217__boxed_51_ = lean_unbox(v___x_47_);
v_res_52_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(v___x_45_, v___x_1216__boxed_50_, v___x_1217__boxed_51_, v_inst_48_, v_____do__lift_49_);
return v_res_52_;
}
}
lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(lean_object* v___x_53_, uint8_t v___x_54_, uint8_t v___x_55_, lean_object* v_inst_56_, lean_object* v_body_57_, lean_object* v_g_58_, lean_object* v_toBind_59_, lean_object* v_x_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_61_ = lean_mk_empty_array_with_capacity(v___x_53_);
v___x_62_ = lean_array_push(v___x_61_, v_x_60_);
v___x_63_ = lean_box(v___x_54_);
v___x_64_ = lean_box(v___x_55_);
lean_inc_ref(v___x_62_);
v___f_65_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_65_, 0, v___x_62_);
lean_closure_set(v___f_65_, 1, v___x_63_);
lean_closure_set(v___f_65_, 2, v___x_64_);
lean_closure_set(v___f_65_, 3, v_inst_56_);
v___x_66_ = lean_expr_instantiate_rev(v_body_57_, v___x_62_);
lean_dec_ref(v___x_62_);
v___x_67_ = lean_apply_1(v_g_58_, v___x_66_);
v___x_68_ = lean_apply_4(v_toBind_59_, lean_box(0), lean_box(0), v___x_67_, v___f_65_);
return v___x_68_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_53_ = stack[0].m_obj;
uint8_t v___x_54_ = stack[1].m_num;
uint8_t v___x_55_ = stack[2].m_num;
lean_object* v_inst_56_ = stack[3].m_obj;
lean_object* v_body_57_ = stack[4].m_obj;
lean_object* v_g_58_ = stack[5].m_obj;
lean_object* v_toBind_59_ = stack[6].m_obj;
lean_object* v_x_60_ = stack[7].m_obj;
lean_object* v_res_69_;
v_res_69_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(v___x_53_, v___x_54_, v___x_55_, v_inst_56_, v_body_57_, v_g_58_, v_toBind_59_, v_x_60_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed(lean_object* v___x_70_, lean_object* v___x_71_, lean_object* v___x_72_, lean_object* v_inst_73_, lean_object* v_body_74_, lean_object* v_g_75_, lean_object* v_toBind_76_, lean_object* v_x_77_){
_start:
{
uint8_t v___x_1265__boxed_78_; uint8_t v___x_1266__boxed_79_; lean_object* v_res_80_; 
v___x_1265__boxed_78_ = lean_unbox(v___x_71_);
v___x_1266__boxed_79_ = lean_unbox(v___x_72_);
v_res_80_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(v___x_70_, v___x_1265__boxed_78_, v___x_1266__boxed_79_, v_inst_73_, v_body_74_, v_g_75_, v_toBind_76_, v_x_77_);
lean_dec_ref(v_body_74_);
lean_dec(v___x_70_);
return v_res_80_;
}
}
lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(lean_object* v___x_81_, uint8_t v___x_82_, uint8_t v___x_83_, lean_object* v_inst_84_, lean_object* v_____do__lift_85_){
_start:
{
uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_86_ = 1;
v___x_87_ = lean_box(v___x_82_);
v___x_88_ = lean_box(v___x_83_);
v___x_89_ = lean_box(v___x_83_);
v___x_90_ = lean_box(v___x_86_);
v___x_91_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_91_, 0, v___x_81_);
lean_closure_set(v___x_91_, 1, v_____do__lift_85_);
lean_closure_set(v___x_91_, 2, v___x_87_);
lean_closure_set(v___x_91_, 3, v___x_88_);
lean_closure_set(v___x_91_, 4, v___x_89_);
lean_closure_set(v___x_91_, 5, v___x_90_);
v___x_92_ = lean_apply_2(v_inst_84_, lean_box(0), v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_81_ = stack[0].m_obj;
uint8_t v___x_82_ = stack[1].m_num;
uint8_t v___x_83_ = stack[2].m_num;
lean_object* v_inst_84_ = stack[3].m_obj;
lean_object* v_____do__lift_85_ = stack[4].m_obj;
lean_object* v_res_93_;
v_res_93_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(v___x_81_, v___x_82_, v___x_83_, v_inst_84_, v_____do__lift_85_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed(lean_object* v___x_94_, lean_object* v___x_95_, lean_object* v___x_96_, lean_object* v_inst_97_, lean_object* v_____do__lift_98_){
_start:
{
uint8_t v___x_1314__boxed_99_; uint8_t v___x_1315__boxed_100_; lean_object* v_res_101_; 
v___x_1314__boxed_99_ = lean_unbox(v___x_95_);
v___x_1315__boxed_100_ = lean_unbox(v___x_96_);
v_res_101_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(v___x_94_, v___x_1314__boxed_99_, v___x_1315__boxed_100_, v_inst_97_, v_____do__lift_98_);
return v_res_101_;
}
}
lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(lean_object* v___x_102_, uint8_t v___x_103_, uint8_t v___x_104_, lean_object* v_inst_105_, lean_object* v_body_106_, lean_object* v_g_107_, lean_object* v_toBind_108_, lean_object* v_x_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_110_ = lean_mk_empty_array_with_capacity(v___x_102_);
v___x_111_ = lean_array_push(v___x_110_, v_x_109_);
v___x_112_ = lean_box(v___x_103_);
v___x_113_ = lean_box(v___x_104_);
lean_inc_ref(v___x_111_);
v___f_114_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_114_, 0, v___x_111_);
lean_closure_set(v___f_114_, 1, v___x_112_);
lean_closure_set(v___f_114_, 2, v___x_113_);
lean_closure_set(v___f_114_, 3, v_inst_105_);
v___x_115_ = lean_expr_instantiate_rev(v_body_106_, v___x_111_);
lean_dec_ref(v___x_111_);
v___x_116_ = lean_apply_1(v_g_107_, v___x_115_);
v___x_117_ = lean_apply_4(v_toBind_108_, lean_box(0), lean_box(0), v___x_116_, v___f_114_);
return v___x_117_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_102_ = stack[0].m_obj;
uint8_t v___x_103_ = stack[1].m_num;
uint8_t v___x_104_ = stack[2].m_num;
lean_object* v_inst_105_ = stack[3].m_obj;
lean_object* v_body_106_ = stack[4].m_obj;
lean_object* v_g_107_ = stack[5].m_obj;
lean_object* v_toBind_108_ = stack[6].m_obj;
lean_object* v_x_109_ = stack[7].m_obj;
lean_object* v_res_118_;
v_res_118_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(v___x_102_, v___x_103_, v___x_104_, v_inst_105_, v_body_106_, v_g_107_, v_toBind_108_, v_x_109_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed(lean_object* v___x_119_, lean_object* v___x_120_, lean_object* v___x_121_, lean_object* v_inst_122_, lean_object* v_body_123_, lean_object* v_g_124_, lean_object* v_toBind_125_, lean_object* v_x_126_){
_start:
{
uint8_t v___x_1360__boxed_127_; uint8_t v___x_1361__boxed_128_; lean_object* v_res_129_; 
v___x_1360__boxed_127_ = lean_unbox(v___x_120_);
v___x_1361__boxed_128_ = lean_unbox(v___x_121_);
v_res_129_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(v___x_119_, v___x_1360__boxed_127_, v___x_1361__boxed_128_, v_inst_122_, v_body_123_, v_g_124_, v_toBind_125_, v_x_126_);
lean_dec_ref(v_body_123_);
lean_dec(v___x_119_);
return v_res_129_;
}
}
lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(lean_object* v_type_130_, lean_object* v_declName_131_, lean_object* v_body_132_, uint8_t v_nondep_133_, lean_object* v_toPure_134_, lean_object* v_value_135_, lean_object* v_e_136_, lean_object* v_____do__lift_137_){
_start:
{
size_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_ptr_addr(v_type_130_);
v___x_139_ = lean_usize_dec_eq(v___x_138_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec_ref(v_e_136_);
v___x_140_ = l_Lean_Expr_letE___override(v_declName_131_, v_type_130_, v_____do__lift_137_, v_body_132_, v_nondep_133_);
v___x_141_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_140_);
return v___x_141_;
}
else
{
size_t v___x_142_; size_t v___x_143_; uint8_t v___x_144_; 
v___x_142_ = lean_ptr_addr(v_value_135_);
v___x_143_ = lean_ptr_addr(v_____do__lift_137_);
v___x_144_ = lean_usize_dec_eq(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec_ref(v_e_136_);
v___x_145_ = l_Lean_Expr_letE___override(v_declName_131_, v_type_130_, v_____do__lift_137_, v_body_132_, v_nondep_133_);
v___x_146_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_145_);
return v___x_146_;
}
else
{
size_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_ptr_addr(v_body_132_);
v___x_148_ = lean_usize_dec_eq(v___x_147_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec_ref(v_e_136_);
v___x_149_ = l_Lean_Expr_letE___override(v_declName_131_, v_type_130_, v_____do__lift_137_, v_body_132_, v_nondep_133_);
v___x_150_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_149_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; 
lean_dec_ref(v_____do__lift_137_);
lean_dec_ref(v_body_132_);
lean_dec(v_declName_131_);
lean_dec_ref(v_type_130_);
v___x_151_ = lean_apply_2(v_toPure_134_, lean_box(0), v_e_136_);
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_130_ = stack[0].m_obj;
lean_object* v_declName_131_ = stack[1].m_obj;
lean_object* v_body_132_ = stack[2].m_obj;
uint8_t v_nondep_133_ = stack[3].m_num;
lean_object* v_toPure_134_ = stack[4].m_obj;
lean_object* v_value_135_ = stack[5].m_obj;
lean_object* v_e_136_ = stack[6].m_obj;
lean_object* v_____do__lift_137_ = stack[7].m_obj;
lean_object* v_res_152_;
v_res_152_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(v_type_130_, v_declName_131_, v_body_132_, v_nondep_133_, v_toPure_134_, v_value_135_, v_e_136_, v_____do__lift_137_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed(lean_object* v_type_153_, lean_object* v_declName_154_, lean_object* v_body_155_, lean_object* v_nondep_156_, lean_object* v_toPure_157_, lean_object* v_value_158_, lean_object* v_e_159_, lean_object* v_____do__lift_160_){
_start:
{
uint8_t v_nondep_1411__boxed_161_; lean_object* v_res_162_; 
v_nondep_1411__boxed_161_ = lean_unbox(v_nondep_156_);
v_res_162_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(v_type_153_, v_declName_154_, v_body_155_, v_nondep_1411__boxed_161_, v_toPure_157_, v_value_158_, v_e_159_, v_____do__lift_160_);
lean_dec_ref(v_value_158_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(lean_object* v_fn_163_, lean_object* v_arg_164_, lean_object* v_toPure_165_, lean_object* v_e_166_, lean_object* v_____do__lift_167_){
_start:
{
size_t v___x_168_; size_t v___x_169_; uint8_t v___x_170_; 
v___x_168_ = lean_ptr_addr(v_fn_163_);
v___x_169_ = lean_ptr_addr(v_____do__lift_167_);
v___x_170_ = lean_usize_dec_eq(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec_ref(v_e_166_);
v___x_171_ = l_Lean_Expr_app___override(v_____do__lift_167_, v_arg_164_);
v___x_172_ = lean_apply_2(v_toPure_165_, lean_box(0), v___x_171_);
return v___x_172_;
}
else
{
size_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_ptr_addr(v_arg_164_);
v___x_174_ = lean_usize_dec_eq(v___x_173_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec_ref(v_e_166_);
v___x_175_ = l_Lean_Expr_app___override(v_____do__lift_167_, v_arg_164_);
v___x_176_ = lean_apply_2(v_toPure_165_, lean_box(0), v___x_175_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; 
lean_dec_ref(v_____do__lift_167_);
lean_dec_ref(v_arg_164_);
v___x_177_ = lean_apply_2(v_toPure_165_, lean_box(0), v_e_166_);
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed(lean_object* v_fn_178_, lean_object* v_arg_179_, lean_object* v_toPure_180_, lean_object* v_e_181_, lean_object* v_____do__lift_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(v_fn_178_, v_arg_179_, v_toPure_180_, v_e_181_, v_____do__lift_182_);
lean_dec_ref(v_fn_178_);
return v_res_183_;
}
}
lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(lean_object* v_binderType_184_, lean_object* v_binderName_185_, lean_object* v_body_186_, uint8_t v_binderInfo_187_, lean_object* v_toPure_188_, lean_object* v_e_189_, lean_object* v_____do__lift_190_){
_start:
{
size_t v___x_191_; size_t v___x_192_; uint8_t v___x_193_; 
v___x_191_ = lean_ptr_addr(v_binderType_184_);
v___x_192_ = lean_ptr_addr(v_____do__lift_190_);
v___x_193_ = lean_usize_dec_eq(v___x_191_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec_ref(v_e_189_);
v___x_194_ = l_Lean_Expr_lam___override(v_binderName_185_, v_____do__lift_190_, v_body_186_, v_binderInfo_187_);
v___x_195_ = lean_apply_2(v_toPure_188_, lean_box(0), v___x_194_);
return v___x_195_;
}
else
{
size_t v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_ptr_addr(v_body_186_);
v___x_197_ = lean_usize_dec_eq(v___x_196_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec_ref(v_e_189_);
v___x_198_ = l_Lean_Expr_lam___override(v_binderName_185_, v_____do__lift_190_, v_body_186_, v_binderInfo_187_);
v___x_199_ = lean_apply_2(v_toPure_188_, lean_box(0), v___x_198_);
return v___x_199_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_187_, v_binderInfo_187_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec_ref(v_e_189_);
v___x_201_ = l_Lean_Expr_lam___override(v_binderName_185_, v_____do__lift_190_, v_body_186_, v_binderInfo_187_);
v___x_202_ = lean_apply_2(v_toPure_188_, lean_box(0), v___x_201_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; 
lean_dec_ref(v_____do__lift_190_);
lean_dec_ref(v_body_186_);
lean_dec(v_binderName_185_);
v___x_203_ = lean_apply_2(v_toPure_188_, lean_box(0), v_e_189_);
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_184_ = stack[0].m_obj;
lean_object* v_binderName_185_ = stack[1].m_obj;
lean_object* v_body_186_ = stack[2].m_obj;
uint8_t v_binderInfo_187_ = stack[3].m_num;
lean_object* v_toPure_188_ = stack[4].m_obj;
lean_object* v_e_189_ = stack[5].m_obj;
lean_object* v_____do__lift_190_ = stack[6].m_obj;
lean_object* v_res_204_;
v_res_204_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(v_binderType_184_, v_binderName_185_, v_body_186_, v_binderInfo_187_, v_toPure_188_, v_e_189_, v_____do__lift_190_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed(lean_object* v_binderType_205_, lean_object* v_binderName_206_, lean_object* v_body_207_, lean_object* v_binderInfo_208_, lean_object* v_toPure_209_, lean_object* v_e_210_, lean_object* v_____do__lift_211_){
_start:
{
uint8_t v_binderInfo_1528__boxed_212_; lean_object* v_res_213_; 
v_binderInfo_1528__boxed_212_ = lean_unbox(v_binderInfo_208_);
v_res_213_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(v_binderType_205_, v_binderName_206_, v_body_207_, v_binderInfo_1528__boxed_212_, v_toPure_209_, v_e_210_, v_____do__lift_211_);
lean_dec_ref(v_binderType_205_);
return v_res_213_;
}
}
lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(lean_object* v_binderType_214_, lean_object* v_binderName_215_, lean_object* v_body_216_, uint8_t v_binderInfo_217_, lean_object* v_toPure_218_, lean_object* v_e_219_, lean_object* v_____do__lift_220_){
_start:
{
size_t v___x_221_; size_t v___x_222_; uint8_t v___x_223_; 
v___x_221_ = lean_ptr_addr(v_binderType_214_);
v___x_222_ = lean_ptr_addr(v_____do__lift_220_);
v___x_223_ = lean_usize_dec_eq(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec_ref(v_e_219_);
v___x_224_ = l_Lean_Expr_forallE___override(v_binderName_215_, v_____do__lift_220_, v_body_216_, v_binderInfo_217_);
v___x_225_ = lean_apply_2(v_toPure_218_, lean_box(0), v___x_224_);
return v___x_225_;
}
else
{
size_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_ptr_addr(v_body_216_);
v___x_227_ = lean_usize_dec_eq(v___x_226_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref(v_e_219_);
v___x_228_ = l_Lean_Expr_forallE___override(v_binderName_215_, v_____do__lift_220_, v_body_216_, v_binderInfo_217_);
v___x_229_ = lean_apply_2(v_toPure_218_, lean_box(0), v___x_228_);
return v___x_229_;
}
else
{
uint8_t v___x_230_; 
v___x_230_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_217_, v_binderInfo_217_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec_ref(v_e_219_);
v___x_231_ = l_Lean_Expr_forallE___override(v_binderName_215_, v_____do__lift_220_, v_body_216_, v_binderInfo_217_);
v___x_232_ = lean_apply_2(v_toPure_218_, lean_box(0), v___x_231_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; 
lean_dec_ref(v_____do__lift_220_);
lean_dec_ref(v_body_216_);
lean_dec(v_binderName_215_);
v___x_233_ = lean_apply_2(v_toPure_218_, lean_box(0), v_e_219_);
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_214_ = stack[0].m_obj;
lean_object* v_binderName_215_ = stack[1].m_obj;
lean_object* v_body_216_ = stack[2].m_obj;
uint8_t v_binderInfo_217_ = stack[3].m_num;
lean_object* v_toPure_218_ = stack[4].m_obj;
lean_object* v_e_219_ = stack[5].m_obj;
lean_object* v_____do__lift_220_ = stack[6].m_obj;
lean_object* v_res_234_;
v_res_234_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(v_binderType_214_, v_binderName_215_, v_body_216_, v_binderInfo_217_, v_toPure_218_, v_e_219_, v_____do__lift_220_);
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed(lean_object* v_binderType_235_, lean_object* v_binderName_236_, lean_object* v_body_237_, lean_object* v_binderInfo_238_, lean_object* v_toPure_239_, lean_object* v_e_240_, lean_object* v_____do__lift_241_){
_start:
{
uint8_t v_binderInfo_1592__boxed_242_; lean_object* v_res_243_; 
v_binderInfo_1592__boxed_242_ = lean_unbox(v_binderInfo_238_);
v_res_243_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(v_binderType_235_, v_binderName_236_, v_body_237_, v_binderInfo_1592__boxed_242_, v_toPure_239_, v_e_240_, v_____do__lift_241_);
lean_dec_ref(v_binderType_235_);
return v_res_243_;
}
}
lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(lean_object* v_type_244_, lean_object* v_declName_245_, lean_object* v_value_246_, lean_object* v_body_247_, uint8_t v_nondep_248_, lean_object* v_toPure_249_, lean_object* v_e_250_, lean_object* v_____do__lift_251_){
_start:
{
size_t v___x_252_; size_t v___x_253_; uint8_t v___x_254_; 
v___x_252_ = lean_ptr_addr(v_type_244_);
v___x_253_ = lean_ptr_addr(v_____do__lift_251_);
v___x_254_ = lean_usize_dec_eq(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref(v_e_250_);
v___x_255_ = l_Lean_Expr_letE___override(v_declName_245_, v_____do__lift_251_, v_value_246_, v_body_247_, v_nondep_248_);
v___x_256_ = lean_apply_2(v_toPure_249_, lean_box(0), v___x_255_);
return v___x_256_;
}
else
{
size_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_ptr_addr(v_value_246_);
v___x_258_ = lean_usize_dec_eq(v___x_257_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref(v_e_250_);
v___x_259_ = l_Lean_Expr_letE___override(v_declName_245_, v_____do__lift_251_, v_value_246_, v_body_247_, v_nondep_248_);
v___x_260_ = lean_apply_2(v_toPure_249_, lean_box(0), v___x_259_);
return v___x_260_;
}
else
{
size_t v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_ptr_addr(v_body_247_);
v___x_262_ = lean_usize_dec_eq(v___x_261_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref(v_e_250_);
v___x_263_ = l_Lean_Expr_letE___override(v_declName_245_, v_____do__lift_251_, v_value_246_, v_body_247_, v_nondep_248_);
v___x_264_ = lean_apply_2(v_toPure_249_, lean_box(0), v___x_263_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; 
lean_dec_ref(v_____do__lift_251_);
lean_dec_ref(v_body_247_);
lean_dec_ref(v_value_246_);
lean_dec(v_declName_245_);
v___x_265_ = lean_apply_2(v_toPure_249_, lean_box(0), v_e_250_);
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_244_ = stack[0].m_obj;
lean_object* v_declName_245_ = stack[1].m_obj;
lean_object* v_value_246_ = stack[2].m_obj;
lean_object* v_body_247_ = stack[3].m_obj;
uint8_t v_nondep_248_ = stack[4].m_num;
lean_object* v_toPure_249_ = stack[5].m_obj;
lean_object* v_e_250_ = stack[6].m_obj;
lean_object* v_____do__lift_251_ = stack[7].m_obj;
lean_object* v_res_266_;
v_res_266_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(v_type_244_, v_declName_245_, v_value_246_, v_body_247_, v_nondep_248_, v_toPure_249_, v_e_250_, v_____do__lift_251_);
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed(lean_object* v_type_267_, lean_object* v_declName_268_, lean_object* v_value_269_, lean_object* v_body_270_, lean_object* v_nondep_271_, lean_object* v_toPure_272_, lean_object* v_e_273_, lean_object* v_____do__lift_274_){
_start:
{
uint8_t v_nondep_1657__boxed_275_; lean_object* v_res_276_; 
v_nondep_1657__boxed_275_ = lean_unbox(v_nondep_271_);
v_res_276_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(v_type_267_, v_declName_268_, v_value_269_, v_body_270_, v_nondep_1657__boxed_275_, v_toPure_272_, v_e_273_, v_____do__lift_274_);
lean_dec_ref(v_type_267_);
return v_res_276_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0));
v___x_279_ = l_Lean_stringToMessageData(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2));
v___x_282_ = l_Lean_stringToMessageData(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4));
v___x_285_ = l_Lean_stringToMessageData(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_g_290_, lean_object* v_n_291_, lean_object* v_e_292_){
_start:
{
lean_object* v_c_294_; lean_object* v_e_295_; lean_object* v_toApplicative_306_; lean_object* v_toBind_307_; lean_object* v_toFunctor_308_; lean_object* v_toPure_309_; lean_object* v_n_311_; lean_object* v_a_312_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_toApplicative_306_ = lean_ctor_get(v_inst_286_, 0);
v_toBind_307_ = lean_ctor_get(v_inst_286_, 1);
v_toFunctor_308_ = lean_ctor_get(v_toApplicative_306_, 0);
v_toPure_309_ = lean_ctor_get(v_toApplicative_306_, 1);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_nat_dec_eq(v_n_291_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_dec_eq(v_n_291_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(2u);
v___x_322_ = lean_nat_dec_eq(v_n_291_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(3u);
v___x_324_ = lean_nat_dec_eq(v_n_291_, v___x_323_);
if (v___x_324_ == 0)
{
if (lean_obj_tag(v_e_292_) == 10)
{
lean_object* v_expr_325_; 
v_expr_325_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref(v_expr_325_);
v_n_311_ = v_n_291_;
v_a_312_ = v_expr_325_;
goto v___jp_310_;
}
else
{
lean_dec(v_g_290_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
v_c_294_ = v_n_291_;
v_e_295_ = v_e_292_;
goto v___jp_293_;
}
}
else
{
lean_dec(v_n_291_);
if (lean_obj_tag(v_e_292_) == 10)
{
lean_object* v_expr_326_; 
v_expr_326_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref(v_expr_326_);
v_n_311_ = v___x_323_;
v_a_312_ = v_expr_326_;
goto v___jp_310_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec_ref(v_e_292_);
lean_dec(v_g_290_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
v___x_327_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5);
v___x_328_ = l_Lean_throwError___redArg(v_inst_286_, v_inst_289_, v___x_327_);
return v___x_328_;
}
}
}
else
{
lean_dec(v_n_291_);
switch(lean_obj_tag(v_e_292_))
{
case 8:
{
lean_object* v_declName_329_; lean_object* v_type_330_; lean_object* v_value_331_; lean_object* v_body_332_; uint8_t v_nondep_333_; lean_object* v___f_334_; uint8_t v___x_335_; lean_object* v___x_336_; 
lean_dec_ref(v_inst_289_);
v_declName_329_ = lean_ctor_get(v_e_292_, 0);
lean_inc(v_declName_329_);
v_type_330_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref(v_type_330_);
v_value_331_ = lean_ctor_get(v_e_292_, 2);
lean_inc_ref(v_value_331_);
v_body_332_ = lean_ctor_get(v_e_292_, 3);
lean_inc_ref(v_body_332_);
v_nondep_333_ = lean_ctor_get_uint8(v_e_292_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_292_, 4);
v___f_334_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_334_, 0, v_body_332_);
lean_closure_set(v___f_334_, 1, v_g_290_);
v___x_335_ = 0;
v___x_336_ = l_Lean_Meta_mapLetDecl___redArg(v_inst_288_, v_inst_286_, v_inst_287_, v_declName_329_, v_type_330_, v_value_331_, v___f_334_, v_nondep_333_, v___x_335_, v___x_320_);
return v___x_336_;
}
case 10:
{
lean_object* v_expr_337_; 
v_expr_337_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref(v_expr_337_);
v_n_311_ = v___x_321_;
v_a_312_ = v_expr_337_;
goto v___jp_310_;
}
default: 
{
lean_dec(v_g_290_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
v_c_294_ = v___x_321_;
v_e_295_ = v_e_292_;
goto v___jp_293_;
}
}
}
}
else
{
lean_dec(v_n_291_);
switch(lean_obj_tag(v_e_292_))
{
case 5:
{
lean_object* v_fn_338_; lean_object* v_arg_339_; lean_object* v___f_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
lean_inc(v_toPure_309_);
lean_inc(v_toBind_307_);
lean_dec_ref(v_inst_289_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
lean_dec_ref(v_inst_286_);
v_fn_338_ = lean_ctor_get(v_e_292_, 0);
lean_inc_ref(v_fn_338_);
v_arg_339_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref_n(v_arg_339_, 2);
v___f_340_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_340_, 0, v_fn_338_);
lean_closure_set(v___f_340_, 1, v_toPure_309_);
lean_closure_set(v___f_340_, 2, v_arg_339_);
lean_closure_set(v___f_340_, 3, v_e_292_);
v___x_341_ = lean_apply_1(v_g_290_, v_arg_339_);
v___x_342_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_341_, v___f_340_);
return v___x_342_;
}
case 6:
{
lean_object* v_binderName_343_; lean_object* v_binderType_344_; lean_object* v_body_345_; uint8_t v_binderInfo_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___f_349_; uint8_t v___x_350_; lean_object* v___x_351_; 
lean_dec_ref(v_inst_289_);
v_binderName_343_ = lean_ctor_get(v_e_292_, 0);
lean_inc(v_binderName_343_);
v_binderType_344_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref(v_binderType_344_);
v_body_345_ = lean_ctor_get(v_e_292_, 2);
lean_inc_ref(v_body_345_);
v_binderInfo_346_ = lean_ctor_get_uint8(v_e_292_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_292_, 3);
v___x_347_ = lean_box(v___x_318_);
v___x_348_ = lean_box(v___x_320_);
lean_inc(v_toBind_307_);
v___f_349_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_349_, 0, v___x_319_);
lean_closure_set(v___f_349_, 1, v___x_347_);
lean_closure_set(v___f_349_, 2, v___x_348_);
lean_closure_set(v___f_349_, 3, v_inst_287_);
lean_closure_set(v___f_349_, 4, v_body_345_);
lean_closure_set(v___f_349_, 5, v_g_290_);
lean_closure_set(v___f_349_, 6, v_toBind_307_);
v___x_350_ = 0;
v___x_351_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_288_, v_inst_286_, v_binderName_343_, v_binderInfo_346_, v_binderType_344_, v___f_349_, v___x_350_);
return v___x_351_;
}
case 7:
{
lean_object* v_binderName_352_; lean_object* v_binderType_353_; lean_object* v_body_354_; uint8_t v_binderInfo_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___f_358_; uint8_t v___x_359_; lean_object* v___x_360_; 
lean_dec_ref(v_inst_289_);
v_binderName_352_ = lean_ctor_get(v_e_292_, 0);
lean_inc(v_binderName_352_);
v_binderType_353_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref(v_binderType_353_);
v_body_354_ = lean_ctor_get(v_e_292_, 2);
lean_inc_ref(v_body_354_);
v_binderInfo_355_ = lean_ctor_get_uint8(v_e_292_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_292_, 3);
v___x_356_ = lean_box(v___x_318_);
v___x_357_ = lean_box(v___x_320_);
lean_inc(v_toBind_307_);
v___f_358_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_358_, 0, v___x_319_);
lean_closure_set(v___f_358_, 1, v___x_356_);
lean_closure_set(v___f_358_, 2, v___x_357_);
lean_closure_set(v___f_358_, 3, v_inst_287_);
lean_closure_set(v___f_358_, 4, v_body_354_);
lean_closure_set(v___f_358_, 5, v_g_290_);
lean_closure_set(v___f_358_, 6, v_toBind_307_);
v___x_359_ = 0;
v___x_360_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_288_, v_inst_286_, v_binderName_352_, v_binderInfo_355_, v_binderType_353_, v___f_358_, v___x_359_);
return v___x_360_;
}
case 8:
{
lean_object* v_declName_361_; lean_object* v_type_362_; lean_object* v_value_363_; lean_object* v_body_364_; uint8_t v_nondep_365_; lean_object* v___x_366_; lean_object* v___f_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_inc(v_toPure_309_);
lean_inc(v_toBind_307_);
lean_dec_ref(v_inst_289_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
lean_dec_ref(v_inst_286_);
v_declName_361_ = lean_ctor_get(v_e_292_, 0);
lean_inc(v_declName_361_);
v_type_362_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref(v_type_362_);
v_value_363_ = lean_ctor_get(v_e_292_, 2);
lean_inc_ref_n(v_value_363_, 2);
v_body_364_ = lean_ctor_get(v_e_292_, 3);
lean_inc_ref(v_body_364_);
v_nondep_365_ = lean_ctor_get_uint8(v_e_292_, sizeof(void*)*4 + 8);
v___x_366_ = lean_box(v_nondep_365_);
v___f_367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_367_, 0, v_type_362_);
lean_closure_set(v___f_367_, 1, v_declName_361_);
lean_closure_set(v___f_367_, 2, v_body_364_);
lean_closure_set(v___f_367_, 3, v___x_366_);
lean_closure_set(v___f_367_, 4, v_toPure_309_);
lean_closure_set(v___f_367_, 5, v_value_363_);
lean_closure_set(v___f_367_, 6, v_e_292_);
v___x_368_ = lean_apply_1(v_g_290_, v_value_363_);
v___x_369_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_368_, v___f_367_);
return v___x_369_;
}
case 10:
{
lean_object* v_expr_370_; 
v_expr_370_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref(v_expr_370_);
v_n_311_ = v___x_319_;
v_a_312_ = v_expr_370_;
goto v___jp_310_;
}
default: 
{
lean_dec(v_g_290_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
v_c_294_ = v___x_319_;
v_e_295_ = v_e_292_;
goto v___jp_293_;
}
}
}
}
else
{
lean_dec(v_n_291_);
switch(lean_obj_tag(v_e_292_))
{
case 5:
{
lean_object* v_fn_371_; lean_object* v_arg_372_; lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_inc(v_toPure_309_);
lean_inc(v_toBind_307_);
lean_dec_ref(v_inst_289_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
lean_dec_ref(v_inst_286_);
v_fn_371_ = lean_ctor_get(v_e_292_, 0);
lean_inc_ref_n(v_fn_371_, 2);
v_arg_372_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref(v_arg_372_);
v___f_373_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_373_, 0, v_fn_371_);
lean_closure_set(v___f_373_, 1, v_arg_372_);
lean_closure_set(v___f_373_, 2, v_toPure_309_);
lean_closure_set(v___f_373_, 3, v_e_292_);
v___x_374_ = lean_apply_1(v_g_290_, v_fn_371_);
v___x_375_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_374_, v___f_373_);
return v___x_375_;
}
case 6:
{
lean_object* v_binderName_376_; lean_object* v_binderType_377_; lean_object* v_body_378_; uint8_t v_binderInfo_379_; lean_object* v___x_380_; lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_inc(v_toPure_309_);
lean_inc(v_toBind_307_);
lean_dec_ref(v_inst_289_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
lean_dec_ref(v_inst_286_);
v_binderName_376_ = lean_ctor_get(v_e_292_, 0);
lean_inc(v_binderName_376_);
v_binderType_377_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref_n(v_binderType_377_, 2);
v_body_378_ = lean_ctor_get(v_e_292_, 2);
lean_inc_ref(v_body_378_);
v_binderInfo_379_ = lean_ctor_get_uint8(v_e_292_, sizeof(void*)*3 + 8);
v___x_380_ = lean_box(v_binderInfo_379_);
v___f_381_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed), 7, 6);
lean_closure_set(v___f_381_, 0, v_binderType_377_);
lean_closure_set(v___f_381_, 1, v_binderName_376_);
lean_closure_set(v___f_381_, 2, v_body_378_);
lean_closure_set(v___f_381_, 3, v___x_380_);
lean_closure_set(v___f_381_, 4, v_toPure_309_);
lean_closure_set(v___f_381_, 5, v_e_292_);
v___x_382_ = lean_apply_1(v_g_290_, v_binderType_377_);
v___x_383_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_382_, v___f_381_);
return v___x_383_;
}
case 7:
{
lean_object* v_binderName_384_; lean_object* v_binderType_385_; lean_object* v_body_386_; uint8_t v_binderInfo_387_; lean_object* v___x_388_; lean_object* v___f_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_inc(v_toPure_309_);
lean_inc(v_toBind_307_);
lean_dec_ref(v_inst_289_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
lean_dec_ref(v_inst_286_);
v_binderName_384_ = lean_ctor_get(v_e_292_, 0);
lean_inc(v_binderName_384_);
v_binderType_385_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref_n(v_binderType_385_, 2);
v_body_386_ = lean_ctor_get(v_e_292_, 2);
lean_inc_ref(v_body_386_);
v_binderInfo_387_ = lean_ctor_get_uint8(v_e_292_, sizeof(void*)*3 + 8);
v___x_388_ = lean_box(v_binderInfo_387_);
v___f_389_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_389_, 0, v_binderType_385_);
lean_closure_set(v___f_389_, 1, v_binderName_384_);
lean_closure_set(v___f_389_, 2, v_body_386_);
lean_closure_set(v___f_389_, 3, v___x_388_);
lean_closure_set(v___f_389_, 4, v_toPure_309_);
lean_closure_set(v___f_389_, 5, v_e_292_);
v___x_390_ = lean_apply_1(v_g_290_, v_binderType_385_);
v___x_391_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_390_, v___f_389_);
return v___x_391_;
}
case 8:
{
lean_object* v_declName_392_; lean_object* v_type_393_; lean_object* v_value_394_; lean_object* v_body_395_; uint8_t v_nondep_396_; lean_object* v___x_397_; lean_object* v___f_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
lean_inc(v_toPure_309_);
lean_inc(v_toBind_307_);
lean_dec_ref(v_inst_289_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
lean_dec_ref(v_inst_286_);
v_declName_392_ = lean_ctor_get(v_e_292_, 0);
lean_inc(v_declName_392_);
v_type_393_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref_n(v_type_393_, 2);
v_value_394_ = lean_ctor_get(v_e_292_, 2);
lean_inc_ref(v_value_394_);
v_body_395_ = lean_ctor_get(v_e_292_, 3);
lean_inc_ref(v_body_395_);
v_nondep_396_ = lean_ctor_get_uint8(v_e_292_, sizeof(void*)*4 + 8);
v___x_397_ = lean_box(v_nondep_396_);
v___f_398_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed), 8, 7);
lean_closure_set(v___f_398_, 0, v_type_393_);
lean_closure_set(v___f_398_, 1, v_declName_392_);
lean_closure_set(v___f_398_, 2, v_value_394_);
lean_closure_set(v___f_398_, 3, v_body_395_);
lean_closure_set(v___f_398_, 4, v___x_397_);
lean_closure_set(v___f_398_, 5, v_toPure_309_);
lean_closure_set(v___f_398_, 6, v_e_292_);
v___x_399_ = lean_apply_1(v_g_290_, v_type_393_);
v___x_400_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_399_, v___f_398_);
return v___x_400_;
}
case 11:
{
lean_object* v_struct_401_; lean_object* v_map_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
lean_inc_ref(v_toFunctor_308_);
lean_dec_ref(v_inst_289_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
lean_dec_ref(v_inst_286_);
v_struct_401_ = lean_ctor_get(v_e_292_, 2);
lean_inc_ref(v_struct_401_);
v_map_402_ = lean_ctor_get(v_toFunctor_308_, 0);
lean_inc(v_map_402_);
lean_dec_ref(v_toFunctor_308_);
v___x_403_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_403_, 0, v_e_292_);
v___x_404_ = lean_apply_1(v_g_290_, v_struct_401_);
v___x_405_ = lean_apply_4(v_map_402_, lean_box(0), lean_box(0), v___x_403_, v___x_404_);
return v___x_405_;
}
case 10:
{
lean_object* v_expr_406_; 
v_expr_406_ = lean_ctor_get(v_e_292_, 1);
lean_inc_ref(v_expr_406_);
v_n_311_ = v___x_317_;
v_a_312_ = v_expr_406_;
goto v___jp_310_;
}
default: 
{
lean_dec(v_g_290_);
lean_dec_ref(v_inst_288_);
lean_dec(v_inst_287_);
v_c_294_ = v___x_317_;
v_e_295_ = v_e_292_;
goto v___jp_293_;
}
}
}
v___jp_293_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_296_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1);
v___x_297_ = l_Nat_reprFast(v_c_294_);
v___x_298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
v___x_299_ = l_Lean_MessageData_ofFormat(v___x_298_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_296_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = l_Lean_MessageData_ofExpr(v_e_295_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Lean_throwError___redArg(v_inst_286_, v_inst_289_, v___x_304_);
return v___x_305_;
}
v___jp_310_:
{
lean_object* v_map_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_map_313_ = lean_ctor_get(v_toFunctor_308_, 0);
lean_inc(v_map_313_);
v___x_314_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_314_, 0, v_e_292_);
v___x_315_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(v_inst_286_, v_inst_287_, v_inst_288_, v_inst_289_, v_g_290_, v_n_311_, v_a_312_);
v___x_316_ = lean_apply_4(v_map_313_, lean_box(0), lean_box(0), v___x_314_, v___x_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord(lean_object* v_M_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_g_412_, lean_object* v_n_413_, lean_object* v_e_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(v_inst_408_, v_inst_409_, v_inst_410_, v_inst_411_, v_g_412_, v_n_413_, v_e_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_g_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_421_) == 0)
{
lean_object* v___x_423_; 
lean_dec_ref(v_inst_419_);
lean_dec_ref(v_inst_418_);
lean_dec(v_inst_417_);
lean_dec_ref(v_inst_416_);
v___x_423_ = lean_apply_1(v_g_420_, v_x_422_);
return v___x_423_;
}
else
{
lean_object* v_head_424_; lean_object* v_tail_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_head_424_ = lean_ctor_get(v_x_421_, 0);
lean_inc(v_head_424_);
v_tail_425_ = lean_ctor_get(v_x_421_, 1);
lean_inc(v_tail_425_);
lean_dec_ref_known(v_x_421_, 2);
lean_inc_ref(v_inst_419_);
lean_inc_ref(v_inst_418_);
lean_inc(v_inst_417_);
lean_inc_ref(v_inst_416_);
v___x_426_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg), 7, 6);
lean_closure_set(v___x_426_, 0, v_inst_416_);
lean_closure_set(v___x_426_, 1, v_inst_417_);
lean_closure_set(v___x_426_, 2, v_inst_418_);
lean_closure_set(v___x_426_, 3, v_inst_419_);
lean_closure_set(v___x_426_, 4, v_g_420_);
lean_closure_set(v___x_426_, 5, v_tail_425_);
v___x_427_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(v_inst_416_, v_inst_417_, v_inst_418_, v_inst_419_, v___x_426_, v_head_424_, v_x_422_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux(lean_object* v_M_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_g_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(v_inst_429_, v_inst_430_, v_inst_431_, v_inst_432_, v_g_433_, v_x_434_, v_x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___redArg(lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_replace_441_, lean_object* v_p_442_, lean_object* v_root_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = l_Lean_SubExpr_Pos_toArray(v_p_442_);
v___x_445_ = lean_array_to_list(v___x_444_);
v___x_446_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(v_inst_437_, v_inst_438_, v_inst_439_, v_inst_440_, v_replace_441_, v___x_445_, v_root_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___redArg___boxed(lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_replace_451_, lean_object* v_p_452_, lean_object* v_root_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Meta_replaceSubexpr___redArg(v_inst_447_, v_inst_448_, v_inst_449_, v_inst_450_, v_replace_451_, v_p_452_, v_root_453_);
lean_dec(v_p_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr(lean_object* v_M_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_replace_460_, lean_object* v_p_461_, lean_object* v_root_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Meta_replaceSubexpr___redArg(v_inst_456_, v_inst_457_, v_inst_458_, v_inst_459_, v_replace_460_, v_p_461_, v_root_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___boxed(lean_object* v_M_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_replace_469_, lean_object* v_p_470_, lean_object* v_root_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_replaceSubexpr(v_M_464_, v_inst_465_, v_inst_466_, v_inst_467_, v_inst_468_, v_replace_469_, v_p_470_, v_root_471_);
lean_dec(v_p_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0(lean_object* v_fvars_473_, lean_object* v_k_474_, lean_object* v_body_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_array_push(v_fvars_473_, v_x_476_);
v___x_478_ = lean_apply_2(v_k_474_, v___x_477_, v_body_475_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1(lean_object* v_fvars_479_, lean_object* v_k_480_, lean_object* v_b_481_, lean_object* v_x_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_array_push(v_fvars_479_, v_x_482_);
v___x_484_ = lean_apply_2(v_k_480_, v___x_483_, v_b_481_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0));
v___x_487_ = l_Lean_stringToMessageData(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_k_491_, lean_object* v_fvars_492_, lean_object* v_n_493_, lean_object* v_e_494_){
_start:
{
lean_object* v_c_496_; lean_object* v_e_497_; lean_object* v_n_509_; lean_object* v_y_510_; lean_object* v_b_511_; uint8_t v_c_512_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(3u);
v___x_518_ = lean_nat_dec_eq(v_n_493_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_nat_dec_eq(v_n_493_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_nat_dec_eq(v_n_493_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(2u);
v___x_524_ = lean_nat_dec_eq(v_n_493_, v___x_523_);
if (v___x_524_ == 0)
{
if (lean_obj_tag(v_e_494_) == 10)
{
lean_object* v_expr_525_; 
v_expr_525_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_expr_525_);
lean_dec_ref_known(v_e_494_, 2);
v_e_494_ = v_expr_525_;
goto _start;
}
else
{
lean_dec_ref(v_fvars_492_);
lean_dec(v_k_491_);
lean_dec_ref(v_inst_489_);
v_c_496_ = v_n_493_;
v_e_497_ = v_e_494_;
goto v___jp_495_;
}
}
else
{
lean_dec(v_n_493_);
switch(lean_obj_tag(v_e_494_))
{
case 8:
{
lean_object* v_declName_527_; lean_object* v_type_528_; lean_object* v_value_529_; lean_object* v_body_530_; lean_object* v___f_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; 
lean_dec_ref(v_inst_490_);
v_declName_527_ = lean_ctor_get(v_e_494_, 0);
lean_inc(v_declName_527_);
v_type_528_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_type_528_);
v_value_529_ = lean_ctor_get(v_e_494_, 2);
lean_inc_ref(v_value_529_);
v_body_530_ = lean_ctor_get(v_e_494_, 3);
lean_inc_ref(v_body_530_);
lean_dec_ref_known(v_e_494_, 4);
lean_inc_ref(v_fvars_492_);
v___f_531_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0), 4, 3);
lean_closure_set(v___f_531_, 0, v_fvars_492_);
lean_closure_set(v___f_531_, 1, v_k_491_);
lean_closure_set(v___f_531_, 2, v_body_530_);
v___x_532_ = lean_expr_instantiate_rev(v_type_528_, v_fvars_492_);
lean_dec_ref(v_type_528_);
v___x_533_ = lean_expr_instantiate_rev(v_value_529_, v_fvars_492_);
lean_dec_ref(v_fvars_492_);
lean_dec_ref(v_value_529_);
v___x_534_ = 0;
v___x_535_ = l_Lean_Meta_withLetDecl___redArg(v_inst_489_, v_inst_488_, v_declName_527_, v___x_532_, v___x_533_, v___f_531_, v___x_522_, v___x_534_);
return v___x_535_;
}
case 10:
{
lean_object* v_expr_536_; 
v_expr_536_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_expr_536_);
lean_dec_ref_known(v_e_494_, 2);
v_n_493_ = v___x_523_;
v_e_494_ = v_expr_536_;
goto _start;
}
default: 
{
lean_dec_ref(v_fvars_492_);
lean_dec(v_k_491_);
lean_dec_ref(v_inst_489_);
v_c_496_ = v___x_523_;
v_e_497_ = v_e_494_;
goto v___jp_495_;
}
}
}
}
else
{
lean_dec(v_n_493_);
switch(lean_obj_tag(v_e_494_))
{
case 5:
{
lean_object* v_arg_538_; lean_object* v___x_539_; 
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
lean_dec_ref(v_inst_488_);
v_arg_538_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_arg_538_);
lean_dec_ref_known(v_e_494_, 2);
v___x_539_ = lean_apply_2(v_k_491_, v_fvars_492_, v_arg_538_);
return v___x_539_;
}
case 6:
{
lean_object* v_binderName_540_; lean_object* v_binderType_541_; lean_object* v_body_542_; uint8_t v_binderInfo_543_; 
lean_dec_ref(v_inst_490_);
v_binderName_540_ = lean_ctor_get(v_e_494_, 0);
lean_inc(v_binderName_540_);
v_binderType_541_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_binderType_541_);
v_body_542_ = lean_ctor_get(v_e_494_, 2);
lean_inc_ref(v_body_542_);
v_binderInfo_543_ = lean_ctor_get_uint8(v_e_494_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_494_, 3);
v_n_509_ = v_binderName_540_;
v_y_510_ = v_binderType_541_;
v_b_511_ = v_body_542_;
v_c_512_ = v_binderInfo_543_;
goto v___jp_508_;
}
case 7:
{
lean_object* v_binderName_544_; lean_object* v_binderType_545_; lean_object* v_body_546_; uint8_t v_binderInfo_547_; 
lean_dec_ref(v_inst_490_);
v_binderName_544_ = lean_ctor_get(v_e_494_, 0);
lean_inc(v_binderName_544_);
v_binderType_545_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_binderType_545_);
v_body_546_ = lean_ctor_get(v_e_494_, 2);
lean_inc_ref(v_body_546_);
v_binderInfo_547_ = lean_ctor_get_uint8(v_e_494_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_494_, 3);
v_n_509_ = v_binderName_544_;
v_y_510_ = v_binderType_545_;
v_b_511_ = v_body_546_;
v_c_512_ = v_binderInfo_547_;
goto v___jp_508_;
}
case 8:
{
lean_object* v_value_548_; lean_object* v___x_549_; 
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
lean_dec_ref(v_inst_488_);
v_value_548_ = lean_ctor_get(v_e_494_, 2);
lean_inc_ref(v_value_548_);
lean_dec_ref_known(v_e_494_, 4);
v___x_549_ = lean_apply_2(v_k_491_, v_fvars_492_, v_value_548_);
return v___x_549_;
}
case 10:
{
lean_object* v_expr_550_; 
v_expr_550_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_expr_550_);
lean_dec_ref_known(v_e_494_, 2);
v_n_493_ = v___x_521_;
v_e_494_ = v_expr_550_;
goto _start;
}
default: 
{
lean_dec_ref(v_fvars_492_);
lean_dec(v_k_491_);
lean_dec_ref(v_inst_489_);
v_c_496_ = v___x_521_;
v_e_497_ = v_e_494_;
goto v___jp_495_;
}
}
}
}
else
{
lean_dec(v_n_493_);
switch(lean_obj_tag(v_e_494_))
{
case 5:
{
lean_object* v_fn_552_; lean_object* v___x_553_; 
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
lean_dec_ref(v_inst_488_);
v_fn_552_ = lean_ctor_get(v_e_494_, 0);
lean_inc_ref(v_fn_552_);
lean_dec_ref_known(v_e_494_, 2);
v___x_553_ = lean_apply_2(v_k_491_, v_fvars_492_, v_fn_552_);
return v___x_553_;
}
case 6:
{
lean_object* v_binderType_554_; lean_object* v___x_555_; 
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
lean_dec_ref(v_inst_488_);
v_binderType_554_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_binderType_554_);
lean_dec_ref_known(v_e_494_, 3);
v___x_555_ = lean_apply_2(v_k_491_, v_fvars_492_, v_binderType_554_);
return v___x_555_;
}
case 7:
{
lean_object* v_binderType_556_; lean_object* v___x_557_; 
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
lean_dec_ref(v_inst_488_);
v_binderType_556_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_binderType_556_);
lean_dec_ref_known(v_e_494_, 3);
v___x_557_ = lean_apply_2(v_k_491_, v_fvars_492_, v_binderType_556_);
return v___x_557_;
}
case 8:
{
lean_object* v_type_558_; lean_object* v___x_559_; 
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
lean_dec_ref(v_inst_488_);
v_type_558_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_type_558_);
lean_dec_ref_known(v_e_494_, 4);
v___x_559_ = lean_apply_2(v_k_491_, v_fvars_492_, v_type_558_);
return v___x_559_;
}
case 11:
{
lean_object* v_struct_560_; lean_object* v___x_561_; 
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
lean_dec_ref(v_inst_488_);
v_struct_560_ = lean_ctor_get(v_e_494_, 2);
lean_inc_ref(v_struct_560_);
lean_dec_ref_known(v_e_494_, 3);
v___x_561_ = lean_apply_2(v_k_491_, v_fvars_492_, v_struct_560_);
return v___x_561_;
}
case 10:
{
lean_object* v_expr_562_; 
v_expr_562_ = lean_ctor_get(v_e_494_, 1);
lean_inc_ref(v_expr_562_);
lean_dec_ref_known(v_e_494_, 2);
v_n_493_ = v___x_519_;
v_e_494_ = v_expr_562_;
goto _start;
}
default: 
{
lean_dec_ref(v_fvars_492_);
lean_dec(v_k_491_);
lean_dec_ref(v_inst_489_);
v_c_496_ = v___x_519_;
v_e_497_ = v_e_494_;
goto v___jp_495_;
}
}
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec_ref(v_e_494_);
lean_dec(v_n_493_);
lean_dec_ref(v_fvars_492_);
lean_dec(v_k_491_);
lean_dec_ref(v_inst_489_);
v___x_564_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1);
v___x_565_ = l_Lean_throwError___redArg(v_inst_488_, v_inst_490_, v___x_564_);
return v___x_565_;
}
v___jp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_498_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1);
v___x_499_ = l_Nat_reprFast(v_c_496_);
v___x_500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
v___x_501_ = l_Lean_MessageData_ofFormat(v___x_500_);
v___x_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_498_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
v___x_504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = l_Lean_MessageData_ofExpr(v_e_497_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Lean_throwError___redArg(v_inst_488_, v_inst_490_, v___x_506_);
return v___x_507_;
}
v___jp_508_:
{
lean_object* v___f_513_; lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; 
lean_inc_ref(v_fvars_492_);
v___f_513_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_513_, 0, v_fvars_492_);
lean_closure_set(v___f_513_, 1, v_k_491_);
lean_closure_set(v___f_513_, 2, v_b_511_);
v___x_514_ = lean_expr_instantiate_rev(v_y_510_, v_fvars_492_);
lean_dec_ref(v_fvars_492_);
lean_dec_ref(v_y_510_);
v___x_515_ = 0;
v___x_516_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_489_, v_inst_488_, v_n_509_, v_c_512_, v___x_514_, v___f_513_, v___x_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux(lean_object* v_M_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_00_u03b1_570_, lean_object* v_k_571_, lean_object* v_fvars_572_, lean_object* v_n_573_, lean_object* v_e_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(v_inst_567_, v_inst_568_, v_inst_569_, v_k_571_, v_fvars_572_, v_n_573_, v_e_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(lean_object* v_fvars_576_, lean_object* v_k_577_, lean_object* v_otherFvars_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = l_Array_append___redArg(v_fvars_576_, v_otherFvars_578_);
v___x_581_ = lean_apply_2(v_k_577_, v___x_580_, v___y_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed(lean_object* v_fvars_582_, lean_object* v_k_583_, lean_object* v_otherFvars_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(v_fvars_582_, v_k_583_, v_otherFvars_584_, v___y_585_);
lean_dec_ref(v_otherFvars_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2(lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v___f_593_, lean_object* v_tail_594_, lean_object* v_y_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0));
v___x_597_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(v_inst_589_, v_inst_590_, v_inst_591_, v_inst_592_, v___f_593_, v___x_596_, v_tail_594_, v_y_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_k_602_, lean_object* v_fvars_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec_ref(v_inst_601_);
lean_dec_ref(v_inst_600_);
lean_dec(v_inst_599_);
lean_dec_ref(v_inst_598_);
v___x_606_ = lean_expr_instantiate_rev(v_x_605_, v_fvars_603_);
lean_dec_ref(v_x_605_);
v___x_607_ = lean_apply_2(v_k_602_, v_fvars_603_, v___x_606_);
return v___x_607_;
}
else
{
lean_object* v_toBind_608_; lean_object* v_head_609_; lean_object* v_tail_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_toBind_608_ = lean_ctor_get(v_inst_598_, 1);
v_head_609_ = lean_ctor_get(v_x_604_, 0);
lean_inc(v_head_609_);
v_tail_610_ = lean_ctor_get(v_x_604_, 1);
lean_inc(v_tail_610_);
lean_dec_ref_known(v_x_604_, 2);
v___x_611_ = lean_unsigned_to_nat(3u);
v___x_612_ = lean_nat_dec_eq(v_head_609_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___f_613_; lean_object* v___x_614_; 
lean_inc_ref(v_inst_601_);
lean_inc_ref(v_inst_600_);
lean_inc_ref(v_inst_598_);
v___f_613_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0), 8, 6);
lean_closure_set(v___f_613_, 0, v_inst_598_);
lean_closure_set(v___f_613_, 1, v_inst_599_);
lean_closure_set(v___f_613_, 2, v_inst_600_);
lean_closure_set(v___f_613_, 3, v_inst_601_);
lean_closure_set(v___f_613_, 4, v_k_602_);
lean_closure_set(v___f_613_, 5, v_tail_610_);
v___x_614_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(v_inst_598_, v_inst_600_, v_inst_601_, v___f_613_, v_fvars_603_, v_head_609_, v_x_605_);
return v___x_614_;
}
else
{
lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_inc(v_toBind_608_);
lean_dec(v_head_609_);
lean_inc_ref(v_fvars_603_);
v___f_615_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_615_, 0, v_fvars_603_);
lean_closure_set(v___f_615_, 1, v_k_602_);
lean_inc(v_inst_599_);
v___f_616_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2), 7, 6);
lean_closure_set(v___f_616_, 0, v_inst_598_);
lean_closure_set(v___f_616_, 1, v_inst_599_);
lean_closure_set(v___f_616_, 2, v_inst_600_);
lean_closure_set(v___f_616_, 3, v_inst_601_);
lean_closure_set(v___f_616_, 4, v___f_615_);
lean_closure_set(v___f_616_, 5, v_tail_610_);
v___x_617_ = lean_expr_instantiate_rev(v_x_605_, v_fvars_603_);
lean_dec_ref(v_fvars_603_);
lean_dec_ref(v_x_605_);
v___x_618_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_618_, 0, v___x_617_);
v___x_619_ = lean_apply_2(v_inst_599_, lean_box(0), v___x_618_);
v___x_620_ = lean_apply_4(v_toBind_608_, lean_box(0), lean_box(0), v___x_619_, v___f_616_);
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0(lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_k_625_, lean_object* v_tail_626_, lean_object* v_fvars_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(v_inst_621_, v_inst_622_, v_inst_623_, v_inst_624_, v_k_625_, v_fvars_627_, v_tail_626_, v___y_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux(lean_object* v_M_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_00_u03b1_635_, lean_object* v_k_636_, lean_object* v_fvars_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(v_inst_631_, v_inst_632_, v_inst_633_, v_inst_634_, v_k_636_, v_fvars_637_, v_x_638_, v_x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___redArg(lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_visit_645_, lean_object* v_p_646_, lean_object* v_root_647_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0));
v___x_649_ = l_Lean_SubExpr_Pos_toArray(v_p_646_);
v___x_650_ = lean_array_to_list(v___x_649_);
v___x_651_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(v_inst_641_, v_inst_642_, v_inst_643_, v_inst_644_, v_visit_645_, v___x_648_, v___x_650_, v_root_647_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___redArg___boxed(lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_visit_656_, lean_object* v_p_657_, lean_object* v_root_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Meta_viewSubexpr___redArg(v_inst_652_, v_inst_653_, v_inst_654_, v_inst_655_, v_visit_656_, v_p_657_, v_root_658_);
lean_dec(v_p_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr(lean_object* v_M_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_00_u03b1_665_, lean_object* v_visit_666_, lean_object* v_p_667_, lean_object* v_root_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Meta_viewSubexpr___redArg(v_inst_661_, v_inst_662_, v_inst_663_, v_inst_664_, v_visit_666_, v_p_667_, v_root_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___boxed(lean_object* v_M_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_00_u03b1_675_, lean_object* v_visit_676_, lean_object* v_p_677_, lean_object* v_root_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Meta_viewSubexpr(v_M_670_, v_inst_671_, v_inst_672_, v_inst_673_, v_inst_674_, v_00_u03b1_675_, v_visit_676_, v_p_677_, v_root_678_);
lean_dec(v_p_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(lean_object* v_fvars_680_, lean_object* v_k_681_, lean_object* v_otherFvars_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = l_Array_append___redArg(v_fvars_680_, v_otherFvars_682_);
v___x_687_ = lean_apply_4(v_k_681_, v___x_686_, v___y_683_, v___y_684_, v___y_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed(lean_object* v_fvars_688_, lean_object* v_k_689_, lean_object* v_otherFvars_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(v_fvars_688_, v_k_689_, v_otherFvars_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec_ref(v_otherFvars_690_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2(lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v___f_699_, lean_object* v_tail_700_, lean_object* v_y_701_, lean_object* v_acc_702_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0));
v___x_704_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(v_inst_695_, v_inst_696_, v_inst_697_, v_inst_698_, v___f_699_, v_acc_702_, v_tail_700_, v___x_703_, v_y_701_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3(lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v___f_709_, lean_object* v_tail_710_, lean_object* v_k_711_, lean_object* v_fvars_712_, lean_object* v_current_713_, lean_object* v___x_714_, lean_object* v_acc_715_, lean_object* v_toBind_716_, lean_object* v_y_717_){
_start:
{
lean_object* v___f_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___f_718_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2), 8, 7);
lean_closure_set(v___f_718_, 0, v_inst_705_);
lean_closure_set(v___f_718_, 1, v_inst_706_);
lean_closure_set(v___f_718_, 2, v_inst_707_);
lean_closure_set(v___f_718_, 3, v_inst_708_);
lean_closure_set(v___f_718_, 4, v___f_709_);
lean_closure_set(v___f_718_, 5, v_tail_710_);
lean_closure_set(v___f_718_, 6, v_y_717_);
v___x_719_ = lean_apply_4(v_k_711_, v_fvars_712_, v_current_713_, v___x_714_, v_acc_715_);
v___x_720_ = lean_apply_4(v_toBind_716_, lean_box(0), lean_box(0), v___x_719_, v___f_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_k_725_, lean_object* v_acc_726_, lean_object* v_address_727_, lean_object* v_fvars_728_, lean_object* v_current_729_){
_start:
{
if (lean_obj_tag(v_address_727_) == 0)
{
lean_object* v_toApplicative_730_; lean_object* v_toPure_731_; lean_object* v___x_732_; 
v_toApplicative_730_ = lean_ctor_get(v_inst_721_, 0);
lean_inc_ref(v_toApplicative_730_);
lean_dec_ref(v_current_729_);
lean_dec_ref(v_fvars_728_);
lean_dec(v_k_725_);
lean_dec_ref(v_inst_724_);
lean_dec_ref(v_inst_723_);
lean_dec(v_inst_722_);
lean_dec_ref(v_inst_721_);
v_toPure_731_ = lean_ctor_get(v_toApplicative_730_, 1);
lean_inc(v_toPure_731_);
lean_dec_ref(v_toApplicative_730_);
v___x_732_ = lean_apply_2(v_toPure_731_, lean_box(0), v_acc_726_);
return v___x_732_;
}
else
{
lean_object* v_toBind_733_; lean_object* v_head_734_; lean_object* v_tail_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_toBind_733_ = lean_ctor_get(v_inst_721_, 1);
lean_inc(v_toBind_733_);
v_head_734_ = lean_ctor_get(v_address_727_, 0);
lean_inc(v_head_734_);
v_tail_735_ = lean_ctor_get(v_address_727_, 1);
lean_inc(v_tail_735_);
lean_dec_ref_known(v_address_727_, 2);
v___x_736_ = lean_unsigned_to_nat(3u);
v___x_737_ = lean_nat_dec_eq(v_head_734_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___f_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_inc_ref(v_current_729_);
lean_inc(v_head_734_);
lean_inc_ref(v_fvars_728_);
lean_inc(v_k_725_);
v___f_738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0), 10, 9);
lean_closure_set(v___f_738_, 0, v_inst_721_);
lean_closure_set(v___f_738_, 1, v_inst_722_);
lean_closure_set(v___f_738_, 2, v_inst_723_);
lean_closure_set(v___f_738_, 3, v_inst_724_);
lean_closure_set(v___f_738_, 4, v_k_725_);
lean_closure_set(v___f_738_, 5, v_tail_735_);
lean_closure_set(v___f_738_, 6, v_fvars_728_);
lean_closure_set(v___f_738_, 7, v_head_734_);
lean_closure_set(v___f_738_, 8, v_current_729_);
v___x_739_ = lean_expr_instantiate_rev(v_current_729_, v_fvars_728_);
lean_dec_ref(v_current_729_);
v___x_740_ = lean_apply_4(v_k_725_, v_fvars_728_, v___x_739_, v_head_734_, v_acc_726_);
v___x_741_ = lean_apply_4(v_toBind_733_, lean_box(0), lean_box(0), v___x_740_, v___f_738_);
return v___x_741_;
}
else
{
lean_object* v___f_742_; lean_object* v_current_743_; lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v_head_734_);
lean_inc(v_k_725_);
lean_inc_ref(v_fvars_728_);
v___f_742_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_742_, 0, v_fvars_728_);
lean_closure_set(v___f_742_, 1, v_k_725_);
v_current_743_ = lean_expr_instantiate_rev(v_current_729_, v_fvars_728_);
lean_dec_ref(v_current_729_);
lean_inc(v_toBind_733_);
lean_inc_ref(v_current_743_);
lean_inc(v_inst_722_);
v___f_744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3), 13, 12);
lean_closure_set(v___f_744_, 0, v_inst_721_);
lean_closure_set(v___f_744_, 1, v_inst_722_);
lean_closure_set(v___f_744_, 2, v_inst_723_);
lean_closure_set(v___f_744_, 3, v_inst_724_);
lean_closure_set(v___f_744_, 4, v___f_742_);
lean_closure_set(v___f_744_, 5, v_tail_735_);
lean_closure_set(v___f_744_, 6, v_k_725_);
lean_closure_set(v___f_744_, 7, v_fvars_728_);
lean_closure_set(v___f_744_, 8, v_current_743_);
lean_closure_set(v___f_744_, 9, v___x_736_);
lean_closure_set(v___f_744_, 10, v_acc_726_);
lean_closure_set(v___f_744_, 11, v_toBind_733_);
v___x_745_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_745_, 0, v_current_743_);
v___x_746_ = lean_apply_2(v_inst_722_, lean_box(0), v___x_745_);
v___x_747_ = lean_apply_4(v_toBind_733_, lean_box(0), lean_box(0), v___x_746_, v___f_744_);
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0(lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_k_752_, lean_object* v_tail_753_, lean_object* v_fvars_754_, lean_object* v_head_755_, lean_object* v_current_756_, lean_object* v_acc_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_inc_ref(v_inst_751_);
lean_inc_ref(v_inst_750_);
lean_inc_ref(v_inst_748_);
v___x_758_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg), 9, 7);
lean_closure_set(v___x_758_, 0, v_inst_748_);
lean_closure_set(v___x_758_, 1, v_inst_749_);
lean_closure_set(v___x_758_, 2, v_inst_750_);
lean_closure_set(v___x_758_, 3, v_inst_751_);
lean_closure_set(v___x_758_, 4, v_k_752_);
lean_closure_set(v___x_758_, 5, v_acc_757_);
lean_closure_set(v___x_758_, 6, v_tail_753_);
v___x_759_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(v_inst_748_, v_inst_750_, v_inst_751_, v___x_758_, v_fvars_754_, v_head_755_, v_current_756_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux(lean_object* v_M_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_00_u03b1_765_, lean_object* v_k_766_, lean_object* v_acc_767_, lean_object* v_address_768_, lean_object* v_fvars_769_, lean_object* v_current_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(v_inst_761_, v_inst_762_, v_inst_763_, v_inst_764_, v_k_766_, v_acc_767_, v_address_768_, v_fvars_769_, v_current_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___redArg(lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_k_776_, lean_object* v_init_777_, lean_object* v_p_778_, lean_object* v_e_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = l_Lean_SubExpr_Pos_toArray(v_p_778_);
v___x_781_ = lean_array_to_list(v___x_780_);
v___x_782_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0));
v___x_783_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(v_inst_772_, v_inst_773_, v_inst_774_, v_inst_775_, v_k_776_, v_init_777_, v___x_781_, v___x_782_, v_e_779_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___redArg___boxed(lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_k_788_, lean_object* v_init_789_, lean_object* v_p_790_, lean_object* v_e_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Meta_foldAncestors___redArg(v_inst_784_, v_inst_785_, v_inst_786_, v_inst_787_, v_k_788_, v_init_789_, v_p_790_, v_e_791_);
lean_dec(v_p_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors(lean_object* v_M_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_00_u03b1_798_, lean_object* v_k_799_, lean_object* v_init_800_, lean_object* v_p_801_, lean_object* v_e_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_foldAncestors___redArg(v_inst_794_, v_inst_795_, v_inst_796_, v_inst_797_, v_k_799_, v_init_800_, v_p_801_, v_e_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___boxed(lean_object* v_M_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_00_u03b1_809_, lean_object* v_k_810_, lean_object* v_init_811_, lean_object* v_p_812_, lean_object* v_e_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Meta_foldAncestors(v_M_804_, v_inst_805_, v_inst_806_, v_inst_807_, v_inst_808_, v_00_u03b1_809_, v_k_810_, v_init_811_, v_p_812_, v_e_813_);
lean_dec(v_p_812_);
return v_res_814_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0));
v___x_817_ = l_Lean_stringToMessageData(v___x_816_);
return v___x_817_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2));
v___x_820_ = l_Lean_stringToMessageData(v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_e_823_, lean_object* v_n_824_){
_start:
{
lean_object* v_e_826_; lean_object* v_c_827_; lean_object* v_toApplicative_838_; lean_object* v_toPure_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_toApplicative_838_ = lean_ctor_get(v_inst_821_, 0);
v_toPure_839_ = lean_ctor_get(v_toApplicative_838_, 1);
v___x_840_ = lean_unsigned_to_nat(3u);
v___x_841_ = lean_nat_dec_eq(v_n_824_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_nat_dec_eq(v_n_824_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_nat_dec_eq(v_n_824_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(2u);
v___x_847_ = lean_nat_dec_eq(v_n_824_, v___x_846_);
if (v___x_847_ == 0)
{
if (lean_obj_tag(v_e_823_) == 10)
{
lean_object* v_expr_848_; 
v_expr_848_ = lean_ctor_get(v_e_823_, 1);
lean_inc_ref(v_expr_848_);
lean_dec_ref_known(v_e_823_, 2);
v_e_823_ = v_expr_848_;
goto _start;
}
else
{
v_e_826_ = v_e_823_;
v_c_827_ = v_n_824_;
goto v___jp_825_;
}
}
else
{
lean_dec(v_n_824_);
switch(lean_obj_tag(v_e_823_))
{
case 8:
{
lean_object* v_body_850_; lean_object* v___x_851_; 
lean_inc(v_toPure_839_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
v_body_850_ = lean_ctor_get(v_e_823_, 3);
lean_inc_ref(v_body_850_);
lean_dec_ref_known(v_e_823_, 4);
v___x_851_ = lean_apply_2(v_toPure_839_, lean_box(0), v_body_850_);
return v___x_851_;
}
case 10:
{
lean_object* v_expr_852_; 
v_expr_852_ = lean_ctor_get(v_e_823_, 1);
lean_inc_ref(v_expr_852_);
lean_dec_ref_known(v_e_823_, 2);
v_e_823_ = v_expr_852_;
v_n_824_ = v___x_846_;
goto _start;
}
default: 
{
v_e_826_ = v_e_823_;
v_c_827_ = v___x_846_;
goto v___jp_825_;
}
}
}
}
else
{
lean_dec(v_n_824_);
switch(lean_obj_tag(v_e_823_))
{
case 5:
{
lean_object* v_arg_854_; lean_object* v___x_855_; 
lean_inc(v_toPure_839_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
v_arg_854_ = lean_ctor_get(v_e_823_, 1);
lean_inc_ref(v_arg_854_);
lean_dec_ref_known(v_e_823_, 2);
v___x_855_ = lean_apply_2(v_toPure_839_, lean_box(0), v_arg_854_);
return v___x_855_;
}
case 6:
{
lean_object* v_body_856_; lean_object* v___x_857_; 
lean_inc(v_toPure_839_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
v_body_856_ = lean_ctor_get(v_e_823_, 2);
lean_inc_ref(v_body_856_);
lean_dec_ref_known(v_e_823_, 3);
v___x_857_ = lean_apply_2(v_toPure_839_, lean_box(0), v_body_856_);
return v___x_857_;
}
case 7:
{
lean_object* v_body_858_; lean_object* v___x_859_; 
lean_inc(v_toPure_839_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
v_body_858_ = lean_ctor_get(v_e_823_, 2);
lean_inc_ref(v_body_858_);
lean_dec_ref_known(v_e_823_, 3);
v___x_859_ = lean_apply_2(v_toPure_839_, lean_box(0), v_body_858_);
return v___x_859_;
}
case 8:
{
lean_object* v_value_860_; lean_object* v___x_861_; 
lean_inc(v_toPure_839_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
v_value_860_ = lean_ctor_get(v_e_823_, 2);
lean_inc_ref(v_value_860_);
lean_dec_ref_known(v_e_823_, 4);
v___x_861_ = lean_apply_2(v_toPure_839_, lean_box(0), v_value_860_);
return v___x_861_;
}
case 10:
{
lean_object* v_expr_862_; 
v_expr_862_ = lean_ctor_get(v_e_823_, 1);
lean_inc_ref(v_expr_862_);
lean_dec_ref_known(v_e_823_, 2);
v_e_823_ = v_expr_862_;
v_n_824_ = v___x_844_;
goto _start;
}
default: 
{
v_e_826_ = v_e_823_;
v_c_827_ = v___x_844_;
goto v___jp_825_;
}
}
}
}
else
{
lean_dec(v_n_824_);
switch(lean_obj_tag(v_e_823_))
{
case 5:
{
lean_object* v_fn_864_; lean_object* v___x_865_; 
lean_inc(v_toPure_839_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
v_fn_864_ = lean_ctor_get(v_e_823_, 0);
lean_inc_ref(v_fn_864_);
lean_dec_ref_known(v_e_823_, 2);
v___x_865_ = lean_apply_2(v_toPure_839_, lean_box(0), v_fn_864_);
return v___x_865_;
}
case 6:
{
lean_object* v_binderType_866_; lean_object* v___x_867_; 
lean_inc(v_toPure_839_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
v_binderType_866_ = lean_ctor_get(v_e_823_, 1);
lean_inc_ref(v_binderType_866_);
lean_dec_ref_known(v_e_823_, 3);
v___x_867_ = lean_apply_2(v_toPure_839_, lean_box(0), v_binderType_866_);
return v___x_867_;
}
case 7:
{
lean_object* v_binderType_868_; lean_object* v___x_869_; 
lean_inc(v_toPure_839_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
v_binderType_868_ = lean_ctor_get(v_e_823_, 1);
lean_inc_ref(v_binderType_868_);
lean_dec_ref_known(v_e_823_, 3);
v___x_869_ = lean_apply_2(v_toPure_839_, lean_box(0), v_binderType_868_);
return v___x_869_;
}
case 8:
{
lean_object* v_type_870_; lean_object* v___x_871_; 
lean_inc(v_toPure_839_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
v_type_870_ = lean_ctor_get(v_e_823_, 1);
lean_inc_ref(v_type_870_);
lean_dec_ref_known(v_e_823_, 4);
v___x_871_ = lean_apply_2(v_toPure_839_, lean_box(0), v_type_870_);
return v___x_871_;
}
case 11:
{
lean_object* v_struct_872_; lean_object* v___x_873_; 
lean_inc(v_toPure_839_);
lean_dec_ref(v_inst_822_);
lean_dec_ref(v_inst_821_);
v_struct_872_ = lean_ctor_get(v_e_823_, 2);
lean_inc_ref(v_struct_872_);
lean_dec_ref_known(v_e_823_, 3);
v___x_873_ = lean_apply_2(v_toPure_839_, lean_box(0), v_struct_872_);
return v___x_873_;
}
case 10:
{
lean_object* v_expr_874_; 
v_expr_874_ = lean_ctor_get(v_e_823_, 1);
lean_inc_ref(v_expr_874_);
lean_dec_ref_known(v_e_823_, 2);
v_e_823_ = v_expr_874_;
v_n_824_ = v___x_842_;
goto _start;
}
default: 
{
v_e_826_ = v_e_823_;
v_c_827_ = v___x_842_;
goto v___jp_825_;
}
}
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v_n_824_);
v___x_876_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3, &l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3);
v___x_877_ = l_Lean_MessageData_ofExpr(v_e_823_);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Lean_throwError___redArg(v_inst_821_, v_inst_822_, v___x_878_);
return v___x_879_;
}
v___jp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_828_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1, &l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1);
v___x_829_ = l_Nat_reprFast(v_c_827_);
v___x_830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
v___x_831_ = l_Lean_MessageData_ofFormat(v___x_830_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_828_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Lean_MessageData_ofExpr(v_e_826_);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = l_Lean_throwError___redArg(v_inst_821_, v_inst_822_, v___x_836_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw(lean_object* v_M_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_e_883_, lean_object* v_n_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(v_inst_881_, v_inst_882_, v_e_883_, v_n_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewSubexpr___redArg(lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v_p_888_, lean_object* v_root_889_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_inc_ref(v_inst_886_);
v___x_890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw), 5, 3);
lean_closure_set(v___x_890_, 0, lean_box(0));
lean_closure_set(v___x_890_, 1, v_inst_886_);
lean_closure_set(v___x_890_, 2, v_inst_887_);
v___x_891_ = l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_886_, v___x_890_, v_root_889_, v_p_888_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewSubexpr(lean_object* v_M_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_p_895_, lean_object* v_root_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Core_viewSubexpr___redArg(v_inst_893_, v_inst_894_, v_p_895_, v_root_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
lean_object* v_n_901_; lean_object* v_y_902_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_dec_eq(v_x_898_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_unsigned_to_nat(2u);
v___x_908_ = lean_nat_dec_eq(v_x_898_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
lean_dec_ref(v_x_899_);
v___x_909_ = lean_box(0);
return v___x_909_;
}
else
{
if (lean_obj_tag(v_x_899_) == 8)
{
lean_object* v_declName_910_; lean_object* v_type_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_declName_910_ = lean_ctor_get(v_x_899_, 0);
lean_inc(v_declName_910_);
v_type_911_ = lean_ctor_get(v_x_899_, 1);
lean_inc_ref(v_type_911_);
lean_dec_ref_known(v_x_899_, 4);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_declName_910_);
lean_ctor_set(v___x_912_, 1, v_type_911_);
v___x_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
else
{
lean_object* v___x_914_; 
lean_dec_ref(v_x_899_);
v___x_914_ = lean_box(0);
return v___x_914_;
}
}
}
else
{
switch(lean_obj_tag(v_x_899_))
{
case 6:
{
lean_object* v_binderName_915_; lean_object* v_binderType_916_; 
v_binderName_915_ = lean_ctor_get(v_x_899_, 0);
lean_inc(v_binderName_915_);
v_binderType_916_ = lean_ctor_get(v_x_899_, 1);
lean_inc_ref(v_binderType_916_);
lean_dec_ref_known(v_x_899_, 3);
v_n_901_ = v_binderName_915_;
v_y_902_ = v_binderType_916_;
goto v___jp_900_;
}
case 7:
{
lean_object* v_binderName_917_; lean_object* v_binderType_918_; 
v_binderName_917_ = lean_ctor_get(v_x_899_, 0);
lean_inc(v_binderName_917_);
v_binderType_918_ = lean_ctor_get(v_x_899_, 1);
lean_inc_ref(v_binderType_918_);
lean_dec_ref_known(v_x_899_, 3);
v_n_901_ = v_binderName_917_;
v_y_902_ = v_binderType_918_;
goto v___jp_900_;
}
default: 
{
lean_object* v___x_919_; 
lean_dec_ref(v_x_899_);
v___x_919_ = lean_box(0);
return v___x_919_;
}
}
}
v___jp_900_:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v_n_901_);
lean_ctor_set(v___x_903_, 1, v_y_902_);
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___boxed(lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(v_x_920_, v_x_921_);
lean_dec(v_x_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__0(lean_object* v_toPure_923_, lean_object* v_c_924_, lean_object* v_snd_925_, lean_object* v_fst_926_, lean_object* v_e_u2082_927_){
_start:
{
lean_object* v___y_929_; lean_object* v___x_932_; 
v___x_932_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(v_c_924_, v_snd_925_);
if (lean_obj_tag(v___x_932_) == 0)
{
v___y_929_ = v_fst_926_;
goto v___jp_928_;
}
else
{
lean_object* v_val_933_; lean_object* v___x_934_; 
v_val_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_val_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = lean_array_push(v_fst_926_, v_val_933_);
v___y_929_ = v___x_934_;
goto v___jp_928_;
}
v___jp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___y_929_);
lean_ctor_set(v___x_930_, 1, v_e_u2082_927_);
v___x_931_ = lean_apply_2(v_toPure_923_, lean_box(0), v___x_930_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__0___boxed(lean_object* v_toPure_935_, lean_object* v_c_936_, lean_object* v_snd_937_, lean_object* v_fst_938_, lean_object* v_e_u2082_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Core_viewBinders___redArg___lam__0(v_toPure_935_, v_c_936_, v_snd_937_, v_fst_938_, v_e_u2082_939_);
lean_dec(v_c_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__1(lean_object* v_toPure_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_toBind_944_, lean_object* v_x_945_, lean_object* v_c_946_){
_start:
{
lean_object* v_fst_947_; lean_object* v_snd_948_; lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_fst_947_ = lean_ctor_get(v_x_945_, 0);
lean_inc(v_fst_947_);
v_snd_948_ = lean_ctor_get(v_x_945_, 1);
lean_inc_n(v_snd_948_, 2);
lean_dec_ref(v_x_945_);
lean_inc(v_c_946_);
v___f_949_ = lean_alloc_closure((void*)(l_Lean_Core_viewBinders___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_949_, 0, v_toPure_941_);
lean_closure_set(v___f_949_, 1, v_c_946_);
lean_closure_set(v___f_949_, 2, v_snd_948_);
lean_closure_set(v___f_949_, 3, v_fst_947_);
v___x_950_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(v_inst_942_, v_inst_943_, v_snd_948_, v_c_946_);
v___x_951_ = lean_apply_4(v_toBind_944_, lean_box(0), lean_box(0), v___x_950_, v___f_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__2(lean_object* v_toPure_952_, lean_object* v_____x_953_){
_start:
{
lean_object* v_fst_954_; lean_object* v___x_955_; 
v_fst_954_ = lean_ctor_get(v_____x_953_, 0);
lean_inc(v_fst_954_);
lean_dec_ref(v_____x_953_);
v___x_955_ = lean_apply_2(v_toPure_952_, lean_box(0), v_fst_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg(lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_p_960_, lean_object* v_root_961_){
_start:
{
lean_object* v_toApplicative_962_; lean_object* v_toBind_963_; lean_object* v_toPure_964_; lean_object* v___f_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_toApplicative_962_ = lean_ctor_get(v_inst_958_, 0);
v_toBind_963_ = lean_ctor_get(v_inst_958_, 1);
lean_inc_n(v_toBind_963_, 2);
v_toPure_964_ = lean_ctor_get(v_toApplicative_962_, 1);
lean_inc_ref(v_inst_958_);
lean_inc_n(v_toPure_964_, 2);
v___f_965_ = lean_alloc_closure((void*)(l_Lean_Core_viewBinders___redArg___lam__1), 6, 4);
lean_closure_set(v___f_965_, 0, v_toPure_964_);
lean_closure_set(v___f_965_, 1, v_inst_958_);
lean_closure_set(v___f_965_, 2, v_inst_959_);
lean_closure_set(v___f_965_, 3, v_toBind_963_);
v___f_966_ = lean_alloc_closure((void*)(l_Lean_Core_viewBinders___redArg___lam__2), 2, 1);
lean_closure_set(v___f_966_, 0, v_toPure_964_);
v___x_967_ = ((lean_object*)(l_Lean_Core_viewBinders___redArg___closed__0));
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_root_961_);
v___x_969_ = l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_958_, v___f_965_, v___x_968_, v_p_960_);
v___x_970_ = lean_apply_4(v_toBind_963_, lean_box(0), lean_box(0), v___x_969_, v___f_966_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders(lean_object* v_M_971_, lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_p_974_, lean_object* v_root_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Core_viewBinders___redArg(v_inst_972_, v_inst_973_, v_p_974_, v_root_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_numBinders___redArg(lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_p_980_, lean_object* v_e_981_){
_start:
{
lean_object* v_toApplicative_982_; lean_object* v_toFunctor_983_; lean_object* v_map_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_toApplicative_982_ = lean_ctor_get(v_inst_978_, 0);
v_toFunctor_983_ = lean_ctor_get(v_toApplicative_982_, 0);
v_map_984_ = lean_ctor_get(v_toFunctor_983_, 0);
lean_inc(v_map_984_);
v___x_985_ = ((lean_object*)(l_Lean_Core_numBinders___redArg___closed__0));
v___x_986_ = l_Lean_Core_viewBinders___redArg(v_inst_978_, v_inst_979_, v_p_980_, v_e_981_);
v___x_987_ = lean_apply_4(v_map_984_, lean_box(0), lean_box(0), v___x_985_, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_numBinders(lean_object* v_M_988_, lean_object* v_inst_989_, lean_object* v_inst_990_, lean_object* v_p_991_, lean_object* v_e_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Core_numBinders___redArg(v_inst_989_, v_inst_990_, v_p_991_, v_e_992_);
return v___x_993_;
}
}
lean_object* runtime_initialize_Lean_SubExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ExprLens(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_ExprLens(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_SubExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ExprLens(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ExprLens(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_ExprLens(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_ExprLens(builtin);
}
#ifdef __cplusplus
}
#endif
