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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(lean_object* v_fn_10_, lean_object* v_toPure_11_, lean_object* v_e_12_, lean_object* v_arg_13_, lean_object* v_____do__lift_14_){
_start:
{
uint8_t v___y_16_; size_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = lean_ptr_addr(v_fn_10_);
v___x_21_ = lean_usize_dec_eq(v___x_20_, v___x_20_);
if (v___x_21_ == 0)
{
v___y_16_ = v___x_21_;
goto v___jp_15_;
}
else
{
size_t v___x_22_; size_t v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_ptr_addr(v_arg_13_);
v___x_23_ = lean_ptr_addr(v_____do__lift_14_);
v___x_24_ = lean_usize_dec_eq(v___x_22_, v___x_23_);
v___y_16_ = v___x_24_;
goto v___jp_15_;
}
v___jp_15_:
{
if (v___y_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec_ref(v_e_12_);
v___x_17_ = l_Lean_Expr_app___override(v_fn_10_, v_____do__lift_14_);
v___x_18_ = lean_apply_2(v_toPure_11_, lean_box(0), v___x_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; 
lean_dec_ref(v_____do__lift_14_);
lean_dec_ref(v_fn_10_);
v___x_19_ = lean_apply_2(v_toPure_11_, lean_box(0), v_e_12_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed(lean_object* v_fn_25_, lean_object* v_toPure_26_, lean_object* v_e_27_, lean_object* v_arg_28_, lean_object* v_____do__lift_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(v_fn_25_, v_toPure_26_, v_e_27_, v_arg_28_, v_____do__lift_29_);
lean_dec_ref(v_arg_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(lean_object* v___x_31_, uint8_t v___x_32_, uint8_t v___x_33_, lean_object* v_inst_34_, lean_object* v_____do__lift_35_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed(lean_object* v___x_44_, lean_object* v___x_45_, lean_object* v___x_46_, lean_object* v_inst_47_, lean_object* v_____do__lift_48_){
_start:
{
uint8_t v___x_1064__boxed_49_; uint8_t v___x_1065__boxed_50_; lean_object* v_res_51_; 
v___x_1064__boxed_49_ = lean_unbox(v___x_45_);
v___x_1065__boxed_50_ = lean_unbox(v___x_46_);
v_res_51_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(v___x_44_, v___x_1064__boxed_49_, v___x_1065__boxed_50_, v_inst_47_, v_____do__lift_48_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(lean_object* v___x_52_, uint8_t v___x_53_, uint8_t v___x_54_, lean_object* v_inst_55_, lean_object* v_body_56_, lean_object* v_g_57_, lean_object* v_toBind_58_, lean_object* v_x_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_60_ = lean_mk_empty_array_with_capacity(v___x_52_);
v___x_61_ = lean_array_push(v___x_60_, v_x_59_);
v___x_62_ = lean_box(v___x_53_);
v___x_63_ = lean_box(v___x_54_);
lean_inc_ref(v___x_61_);
v___f_64_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_64_, 0, v___x_61_);
lean_closure_set(v___f_64_, 1, v___x_62_);
lean_closure_set(v___f_64_, 2, v___x_63_);
lean_closure_set(v___f_64_, 3, v_inst_55_);
v___x_65_ = lean_expr_instantiate_rev(v_body_56_, v___x_61_);
lean_dec_ref(v___x_61_);
v___x_66_ = lean_apply_1(v_g_57_, v___x_65_);
v___x_67_ = lean_apply_4(v_toBind_58_, lean_box(0), lean_box(0), v___x_66_, v___f_64_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed(lean_object* v___x_68_, lean_object* v___x_69_, lean_object* v___x_70_, lean_object* v_inst_71_, lean_object* v_body_72_, lean_object* v_g_73_, lean_object* v_toBind_74_, lean_object* v_x_75_){
_start:
{
uint8_t v___x_1095__boxed_76_; uint8_t v___x_1096__boxed_77_; lean_object* v_res_78_; 
v___x_1095__boxed_76_ = lean_unbox(v___x_69_);
v___x_1096__boxed_77_ = lean_unbox(v___x_70_);
v_res_78_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(v___x_68_, v___x_1095__boxed_76_, v___x_1096__boxed_77_, v_inst_71_, v_body_72_, v_g_73_, v_toBind_74_, v_x_75_);
lean_dec_ref(v_body_72_);
lean_dec(v___x_68_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(lean_object* v___x_79_, uint8_t v___x_80_, uint8_t v___x_81_, lean_object* v_inst_82_, lean_object* v_____do__lift_83_){
_start:
{
uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_84_ = 1;
v___x_85_ = lean_box(v___x_80_);
v___x_86_ = lean_box(v___x_81_);
v___x_87_ = lean_box(v___x_81_);
v___x_88_ = lean_box(v___x_84_);
v___x_89_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_89_, 0, v___x_79_);
lean_closure_set(v___x_89_, 1, v_____do__lift_83_);
lean_closure_set(v___x_89_, 2, v___x_85_);
lean_closure_set(v___x_89_, 3, v___x_86_);
lean_closure_set(v___x_89_, 4, v___x_87_);
lean_closure_set(v___x_89_, 5, v___x_88_);
v___x_90_ = lean_apply_2(v_inst_82_, lean_box(0), v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed(lean_object* v___x_91_, lean_object* v___x_92_, lean_object* v___x_93_, lean_object* v_inst_94_, lean_object* v_____do__lift_95_){
_start:
{
uint8_t v___x_1126__boxed_96_; uint8_t v___x_1127__boxed_97_; lean_object* v_res_98_; 
v___x_1126__boxed_96_ = lean_unbox(v___x_92_);
v___x_1127__boxed_97_ = lean_unbox(v___x_93_);
v_res_98_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(v___x_91_, v___x_1126__boxed_96_, v___x_1127__boxed_97_, v_inst_94_, v_____do__lift_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(lean_object* v___x_99_, uint8_t v___x_100_, uint8_t v___x_101_, lean_object* v_inst_102_, lean_object* v_body_103_, lean_object* v_g_104_, lean_object* v_toBind_105_, lean_object* v_x_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_107_ = lean_mk_empty_array_with_capacity(v___x_99_);
v___x_108_ = lean_array_push(v___x_107_, v_x_106_);
v___x_109_ = lean_box(v___x_100_);
v___x_110_ = lean_box(v___x_101_);
lean_inc_ref(v___x_108_);
v___f_111_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_111_, 0, v___x_108_);
lean_closure_set(v___f_111_, 1, v___x_109_);
lean_closure_set(v___f_111_, 2, v___x_110_);
lean_closure_set(v___f_111_, 3, v_inst_102_);
v___x_112_ = lean_expr_instantiate_rev(v_body_103_, v___x_108_);
lean_dec_ref(v___x_108_);
v___x_113_ = lean_apply_1(v_g_104_, v___x_112_);
v___x_114_ = lean_apply_4(v_toBind_105_, lean_box(0), lean_box(0), v___x_113_, v___f_111_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed(lean_object* v___x_115_, lean_object* v___x_116_, lean_object* v___x_117_, lean_object* v_inst_118_, lean_object* v_body_119_, lean_object* v_g_120_, lean_object* v_toBind_121_, lean_object* v_x_122_){
_start:
{
uint8_t v___x_1155__boxed_123_; uint8_t v___x_1156__boxed_124_; lean_object* v_res_125_; 
v___x_1155__boxed_123_ = lean_unbox(v___x_116_);
v___x_1156__boxed_124_ = lean_unbox(v___x_117_);
v_res_125_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(v___x_115_, v___x_1155__boxed_123_, v___x_1156__boxed_124_, v_inst_118_, v_body_119_, v_g_120_, v_toBind_121_, v_x_122_);
lean_dec_ref(v_body_119_);
lean_dec(v___x_115_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(lean_object* v_declName_126_, lean_object* v_type_127_, lean_object* v_body_128_, uint8_t v_nondep_129_, lean_object* v_toPure_130_, lean_object* v_e_131_, lean_object* v_value_132_, lean_object* v_____do__lift_133_){
_start:
{
uint8_t v___y_135_; size_t v___x_143_; uint8_t v___x_144_; 
v___x_143_ = lean_ptr_addr(v_type_127_);
v___x_144_ = lean_usize_dec_eq(v___x_143_, v___x_143_);
if (v___x_144_ == 0)
{
v___y_135_ = v___x_144_;
goto v___jp_134_;
}
else
{
size_t v___x_145_; size_t v___x_146_; uint8_t v___x_147_; 
v___x_145_ = lean_ptr_addr(v_value_132_);
v___x_146_ = lean_ptr_addr(v_____do__lift_133_);
v___x_147_ = lean_usize_dec_eq(v___x_145_, v___x_146_);
v___y_135_ = v___x_147_;
goto v___jp_134_;
}
v___jp_134_:
{
if (v___y_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec_ref(v_e_131_);
v___x_136_ = l_Lean_Expr_letE___override(v_declName_126_, v_type_127_, v_____do__lift_133_, v_body_128_, v_nondep_129_);
v___x_137_ = lean_apply_2(v_toPure_130_, lean_box(0), v___x_136_);
return v___x_137_;
}
else
{
size_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_ptr_addr(v_body_128_);
v___x_139_ = lean_usize_dec_eq(v___x_138_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec_ref(v_e_131_);
v___x_140_ = l_Lean_Expr_letE___override(v_declName_126_, v_type_127_, v_____do__lift_133_, v_body_128_, v_nondep_129_);
v___x_141_ = lean_apply_2(v_toPure_130_, lean_box(0), v___x_140_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; 
lean_dec_ref(v_____do__lift_133_);
lean_dec_ref(v_body_128_);
lean_dec_ref(v_type_127_);
lean_dec(v_declName_126_);
v___x_142_ = lean_apply_2(v_toPure_130_, lean_box(0), v_e_131_);
return v___x_142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed(lean_object* v_declName_148_, lean_object* v_type_149_, lean_object* v_body_150_, lean_object* v_nondep_151_, lean_object* v_toPure_152_, lean_object* v_e_153_, lean_object* v_value_154_, lean_object* v_____do__lift_155_){
_start:
{
uint8_t v_nondep_1188__boxed_156_; lean_object* v_res_157_; 
v_nondep_1188__boxed_156_ = lean_unbox(v_nondep_151_);
v_res_157_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(v_declName_148_, v_type_149_, v_body_150_, v_nondep_1188__boxed_156_, v_toPure_152_, v_e_153_, v_value_154_, v_____do__lift_155_);
lean_dec_ref(v_value_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(lean_object* v_arg_158_, lean_object* v_toPure_159_, lean_object* v_e_160_, lean_object* v_fn_161_, lean_object* v_____do__lift_162_){
_start:
{
uint8_t v___y_164_; size_t v___x_168_; size_t v___x_169_; uint8_t v___x_170_; 
v___x_168_ = lean_ptr_addr(v_fn_161_);
v___x_169_ = lean_ptr_addr(v_____do__lift_162_);
v___x_170_ = lean_usize_dec_eq(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
v___y_164_ = v___x_170_;
goto v___jp_163_;
}
else
{
size_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_ptr_addr(v_arg_158_);
v___x_172_ = lean_usize_dec_eq(v___x_171_, v___x_171_);
v___y_164_ = v___x_172_;
goto v___jp_163_;
}
v___jp_163_:
{
if (v___y_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec_ref(v_e_160_);
v___x_165_ = l_Lean_Expr_app___override(v_____do__lift_162_, v_arg_158_);
v___x_166_ = lean_apply_2(v_toPure_159_, lean_box(0), v___x_165_);
return v___x_166_;
}
else
{
lean_object* v___x_167_; 
lean_dec_ref(v_____do__lift_162_);
lean_dec_ref(v_arg_158_);
v___x_167_ = lean_apply_2(v_toPure_159_, lean_box(0), v_e_160_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed(lean_object* v_arg_173_, lean_object* v_toPure_174_, lean_object* v_e_175_, lean_object* v_fn_176_, lean_object* v_____do__lift_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(v_arg_173_, v_toPure_174_, v_e_175_, v_fn_176_, v_____do__lift_177_);
lean_dec_ref(v_fn_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(lean_object* v_binderName_179_, lean_object* v_body_180_, uint8_t v_binderInfo_181_, lean_object* v_toPure_182_, lean_object* v_e_183_, lean_object* v_binderType_184_, lean_object* v_____do__lift_185_){
_start:
{
uint8_t v___y_187_; size_t v___x_194_; size_t v___x_195_; uint8_t v___x_196_; 
v___x_194_ = lean_ptr_addr(v_binderType_184_);
v___x_195_ = lean_ptr_addr(v_____do__lift_185_);
v___x_196_ = lean_usize_dec_eq(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
v___y_187_ = v___x_196_;
goto v___jp_186_;
}
else
{
size_t v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_ptr_addr(v_body_180_);
v___x_198_ = lean_usize_dec_eq(v___x_197_, v___x_197_);
v___y_187_ = v___x_198_;
goto v___jp_186_;
}
v___jp_186_:
{
if (v___y_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec_ref(v_e_183_);
v___x_188_ = l_Lean_Expr_lam___override(v_binderName_179_, v_____do__lift_185_, v_body_180_, v_binderInfo_181_);
v___x_189_ = lean_apply_2(v_toPure_182_, lean_box(0), v___x_188_);
return v___x_189_;
}
else
{
uint8_t v___x_190_; 
v___x_190_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_181_, v_binderInfo_181_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec_ref(v_e_183_);
v___x_191_ = l_Lean_Expr_lam___override(v_binderName_179_, v_____do__lift_185_, v_body_180_, v_binderInfo_181_);
v___x_192_ = lean_apply_2(v_toPure_182_, lean_box(0), v___x_191_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; 
lean_dec_ref(v_____do__lift_185_);
lean_dec_ref(v_body_180_);
lean_dec(v_binderName_179_);
v___x_193_ = lean_apply_2(v_toPure_182_, lean_box(0), v_e_183_);
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed(lean_object* v_binderName_199_, lean_object* v_body_200_, lean_object* v_binderInfo_201_, lean_object* v_toPure_202_, lean_object* v_e_203_, lean_object* v_binderType_204_, lean_object* v_____do__lift_205_){
_start:
{
uint8_t v_binderInfo_1262__boxed_206_; lean_object* v_res_207_; 
v_binderInfo_1262__boxed_206_ = lean_unbox(v_binderInfo_201_);
v_res_207_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(v_binderName_199_, v_body_200_, v_binderInfo_1262__boxed_206_, v_toPure_202_, v_e_203_, v_binderType_204_, v_____do__lift_205_);
lean_dec_ref(v_binderType_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(lean_object* v_binderName_208_, lean_object* v_body_209_, uint8_t v_binderInfo_210_, lean_object* v_toPure_211_, lean_object* v_e_212_, lean_object* v_binderType_213_, lean_object* v_____do__lift_214_){
_start:
{
uint8_t v___y_216_; size_t v___x_223_; size_t v___x_224_; uint8_t v___x_225_; 
v___x_223_ = lean_ptr_addr(v_binderType_213_);
v___x_224_ = lean_ptr_addr(v_____do__lift_214_);
v___x_225_ = lean_usize_dec_eq(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
v___y_216_ = v___x_225_;
goto v___jp_215_;
}
else
{
size_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_ptr_addr(v_body_209_);
v___x_227_ = lean_usize_dec_eq(v___x_226_, v___x_226_);
v___y_216_ = v___x_227_;
goto v___jp_215_;
}
v___jp_215_:
{
if (v___y_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref(v_e_212_);
v___x_217_ = l_Lean_Expr_forallE___override(v_binderName_208_, v_____do__lift_214_, v_body_209_, v_binderInfo_210_);
v___x_218_ = lean_apply_2(v_toPure_211_, lean_box(0), v___x_217_);
return v___x_218_;
}
else
{
uint8_t v___x_219_; 
v___x_219_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_210_, v_binderInfo_210_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec_ref(v_e_212_);
v___x_220_ = l_Lean_Expr_forallE___override(v_binderName_208_, v_____do__lift_214_, v_body_209_, v_binderInfo_210_);
v___x_221_ = lean_apply_2(v_toPure_211_, lean_box(0), v___x_220_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; 
lean_dec_ref(v_____do__lift_214_);
lean_dec_ref(v_body_209_);
lean_dec(v_binderName_208_);
v___x_222_ = lean_apply_2(v_toPure_211_, lean_box(0), v_e_212_);
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed(lean_object* v_binderName_228_, lean_object* v_body_229_, lean_object* v_binderInfo_230_, lean_object* v_toPure_231_, lean_object* v_e_232_, lean_object* v_binderType_233_, lean_object* v_____do__lift_234_){
_start:
{
uint8_t v_binderInfo_1303__boxed_235_; lean_object* v_res_236_; 
v_binderInfo_1303__boxed_235_ = lean_unbox(v_binderInfo_230_);
v_res_236_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(v_binderName_228_, v_body_229_, v_binderInfo_1303__boxed_235_, v_toPure_231_, v_e_232_, v_binderType_233_, v_____do__lift_234_);
lean_dec_ref(v_binderType_233_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(lean_object* v_declName_237_, lean_object* v_value_238_, lean_object* v_body_239_, uint8_t v_nondep_240_, lean_object* v_toPure_241_, lean_object* v_e_242_, lean_object* v_type_243_, lean_object* v_____do__lift_244_){
_start:
{
uint8_t v___y_246_; size_t v___x_254_; size_t v___x_255_; uint8_t v___x_256_; 
v___x_254_ = lean_ptr_addr(v_type_243_);
v___x_255_ = lean_ptr_addr(v_____do__lift_244_);
v___x_256_ = lean_usize_dec_eq(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
v___y_246_ = v___x_256_;
goto v___jp_245_;
}
else
{
size_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_ptr_addr(v_value_238_);
v___x_258_ = lean_usize_dec_eq(v___x_257_, v___x_257_);
v___y_246_ = v___x_258_;
goto v___jp_245_;
}
v___jp_245_:
{
if (v___y_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v_e_242_);
v___x_247_ = l_Lean_Expr_letE___override(v_declName_237_, v_____do__lift_244_, v_value_238_, v_body_239_, v_nondep_240_);
v___x_248_ = lean_apply_2(v_toPure_241_, lean_box(0), v___x_247_);
return v___x_248_;
}
else
{
size_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_ptr_addr(v_body_239_);
v___x_250_ = lean_usize_dec_eq(v___x_249_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref(v_e_242_);
v___x_251_ = l_Lean_Expr_letE___override(v_declName_237_, v_____do__lift_244_, v_value_238_, v_body_239_, v_nondep_240_);
v___x_252_ = lean_apply_2(v_toPure_241_, lean_box(0), v___x_251_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; 
lean_dec_ref(v_____do__lift_244_);
lean_dec_ref(v_body_239_);
lean_dec_ref(v_value_238_);
lean_dec(v_declName_237_);
v___x_253_ = lean_apply_2(v_toPure_241_, lean_box(0), v_e_242_);
return v___x_253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed(lean_object* v_declName_259_, lean_object* v_value_260_, lean_object* v_body_261_, lean_object* v_nondep_262_, lean_object* v_toPure_263_, lean_object* v_e_264_, lean_object* v_type_265_, lean_object* v_____do__lift_266_){
_start:
{
uint8_t v_nondep_1345__boxed_267_; lean_object* v_res_268_; 
v_nondep_1345__boxed_267_ = lean_unbox(v_nondep_262_);
v_res_268_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(v_declName_259_, v_value_260_, v_body_261_, v_nondep_1345__boxed_267_, v_toPure_263_, v_e_264_, v_type_265_, v_____do__lift_266_);
lean_dec_ref(v_type_265_);
return v_res_268_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0));
v___x_271_ = l_Lean_stringToMessageData(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4));
v___x_277_ = l_Lean_stringToMessageData(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_g_282_, lean_object* v_n_283_, lean_object* v_e_284_){
_start:
{
lean_object* v_c_286_; lean_object* v_e_287_; lean_object* v_toApplicative_298_; lean_object* v_toBind_299_; lean_object* v_toFunctor_300_; lean_object* v_toPure_301_; lean_object* v_n_303_; lean_object* v_a_304_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_toApplicative_298_ = lean_ctor_get(v_inst_278_, 0);
v_toBind_299_ = lean_ctor_get(v_inst_278_, 1);
v_toFunctor_300_ = lean_ctor_get(v_toApplicative_298_, 0);
v_toPure_301_ = lean_ctor_get(v_toApplicative_298_, 1);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_nat_dec_eq(v_n_283_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_dec_eq(v_n_283_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(2u);
v___x_314_ = lean_nat_dec_eq(v_n_283_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(3u);
v___x_316_ = lean_nat_dec_eq(v_n_283_, v___x_315_);
if (v___x_316_ == 0)
{
if (lean_obj_tag(v_e_284_) == 10)
{
lean_object* v_expr_317_; 
v_expr_317_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_expr_317_);
v_n_303_ = v_n_283_;
v_a_304_ = v_expr_317_;
goto v___jp_302_;
}
else
{
lean_dec(v_g_282_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
v_c_286_ = v_n_283_;
v_e_287_ = v_e_284_;
goto v___jp_285_;
}
}
else
{
lean_dec(v_n_283_);
if (lean_obj_tag(v_e_284_) == 10)
{
lean_object* v_expr_318_; 
v_expr_318_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_expr_318_);
v_n_303_ = v___x_315_;
v_a_304_ = v_expr_318_;
goto v___jp_302_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_e_284_);
lean_dec(v_g_282_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
v___x_319_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5);
v___x_320_ = l_Lean_throwError___redArg(v_inst_278_, v_inst_281_, v___x_319_);
return v___x_320_;
}
}
}
else
{
lean_dec(v_n_283_);
switch(lean_obj_tag(v_e_284_))
{
case 8:
{
lean_object* v_declName_321_; lean_object* v_type_322_; lean_object* v_value_323_; lean_object* v_body_324_; uint8_t v_nondep_325_; lean_object* v___f_326_; uint8_t v___x_327_; lean_object* v___x_328_; 
lean_dec_ref(v_inst_281_);
v_declName_321_ = lean_ctor_get(v_e_284_, 0);
lean_inc(v_declName_321_);
v_type_322_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_type_322_);
v_value_323_ = lean_ctor_get(v_e_284_, 2);
lean_inc_ref(v_value_323_);
v_body_324_ = lean_ctor_get(v_e_284_, 3);
lean_inc_ref(v_body_324_);
v_nondep_325_ = lean_ctor_get_uint8(v_e_284_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_284_);
v___f_326_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_326_, 0, v_body_324_);
lean_closure_set(v___f_326_, 1, v_g_282_);
v___x_327_ = 0;
v___x_328_ = l_Lean_Meta_mapLetDecl___redArg(v_inst_280_, v_inst_278_, v_inst_279_, v_declName_321_, v_type_322_, v_value_323_, v___f_326_, v_nondep_325_, v___x_327_, v___x_312_);
return v___x_328_;
}
case 10:
{
lean_object* v_expr_329_; 
v_expr_329_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_expr_329_);
v_n_303_ = v___x_313_;
v_a_304_ = v_expr_329_;
goto v___jp_302_;
}
default: 
{
lean_dec(v_g_282_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
v_c_286_ = v___x_313_;
v_e_287_ = v_e_284_;
goto v___jp_285_;
}
}
}
}
else
{
lean_dec(v_n_283_);
switch(lean_obj_tag(v_e_284_))
{
case 5:
{
lean_object* v_fn_330_; lean_object* v_arg_331_; lean_object* v___f_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
lean_inc(v_toPure_301_);
lean_inc(v_toBind_299_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
lean_dec_ref(v_inst_278_);
v_fn_330_ = lean_ctor_get(v_e_284_, 0);
lean_inc_ref(v_fn_330_);
v_arg_331_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref_n(v_arg_331_, 2);
v___f_332_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_332_, 0, v_fn_330_);
lean_closure_set(v___f_332_, 1, v_toPure_301_);
lean_closure_set(v___f_332_, 2, v_e_284_);
lean_closure_set(v___f_332_, 3, v_arg_331_);
v___x_333_ = lean_apply_1(v_g_282_, v_arg_331_);
v___x_334_ = lean_apply_4(v_toBind_299_, lean_box(0), lean_box(0), v___x_333_, v___f_332_);
return v___x_334_;
}
case 6:
{
lean_object* v_binderName_335_; lean_object* v_binderType_336_; lean_object* v_body_337_; uint8_t v_binderInfo_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___f_341_; uint8_t v___x_342_; lean_object* v___x_343_; 
lean_dec_ref(v_inst_281_);
v_binderName_335_ = lean_ctor_get(v_e_284_, 0);
lean_inc(v_binderName_335_);
v_binderType_336_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_binderType_336_);
v_body_337_ = lean_ctor_get(v_e_284_, 2);
lean_inc_ref(v_body_337_);
v_binderInfo_338_ = lean_ctor_get_uint8(v_e_284_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_284_);
v___x_339_ = lean_box(v___x_310_);
v___x_340_ = lean_box(v___x_312_);
lean_inc(v_toBind_299_);
v___f_341_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_341_, 0, v___x_311_);
lean_closure_set(v___f_341_, 1, v___x_339_);
lean_closure_set(v___f_341_, 2, v___x_340_);
lean_closure_set(v___f_341_, 3, v_inst_279_);
lean_closure_set(v___f_341_, 4, v_body_337_);
lean_closure_set(v___f_341_, 5, v_g_282_);
lean_closure_set(v___f_341_, 6, v_toBind_299_);
v___x_342_ = 0;
v___x_343_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_280_, v_inst_278_, v_binderName_335_, v_binderInfo_338_, v_binderType_336_, v___f_341_, v___x_342_);
return v___x_343_;
}
case 7:
{
lean_object* v_binderName_344_; lean_object* v_binderType_345_; lean_object* v_body_346_; uint8_t v_binderInfo_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___f_350_; uint8_t v___x_351_; lean_object* v___x_352_; 
lean_dec_ref(v_inst_281_);
v_binderName_344_ = lean_ctor_get(v_e_284_, 0);
lean_inc(v_binderName_344_);
v_binderType_345_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_binderType_345_);
v_body_346_ = lean_ctor_get(v_e_284_, 2);
lean_inc_ref(v_body_346_);
v_binderInfo_347_ = lean_ctor_get_uint8(v_e_284_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_284_);
v___x_348_ = lean_box(v___x_310_);
v___x_349_ = lean_box(v___x_312_);
lean_inc(v_toBind_299_);
v___f_350_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_350_, 0, v___x_311_);
lean_closure_set(v___f_350_, 1, v___x_348_);
lean_closure_set(v___f_350_, 2, v___x_349_);
lean_closure_set(v___f_350_, 3, v_inst_279_);
lean_closure_set(v___f_350_, 4, v_body_346_);
lean_closure_set(v___f_350_, 5, v_g_282_);
lean_closure_set(v___f_350_, 6, v_toBind_299_);
v___x_351_ = 0;
v___x_352_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_280_, v_inst_278_, v_binderName_344_, v_binderInfo_347_, v_binderType_345_, v___f_350_, v___x_351_);
return v___x_352_;
}
case 8:
{
lean_object* v_declName_353_; lean_object* v_type_354_; lean_object* v_value_355_; lean_object* v_body_356_; uint8_t v_nondep_357_; lean_object* v___x_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_inc(v_toPure_301_);
lean_inc(v_toBind_299_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
lean_dec_ref(v_inst_278_);
v_declName_353_ = lean_ctor_get(v_e_284_, 0);
lean_inc(v_declName_353_);
v_type_354_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_type_354_);
v_value_355_ = lean_ctor_get(v_e_284_, 2);
lean_inc_ref_n(v_value_355_, 2);
v_body_356_ = lean_ctor_get(v_e_284_, 3);
lean_inc_ref(v_body_356_);
v_nondep_357_ = lean_ctor_get_uint8(v_e_284_, sizeof(void*)*4 + 8);
v___x_358_ = lean_box(v_nondep_357_);
v___f_359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_359_, 0, v_declName_353_);
lean_closure_set(v___f_359_, 1, v_type_354_);
lean_closure_set(v___f_359_, 2, v_body_356_);
lean_closure_set(v___f_359_, 3, v___x_358_);
lean_closure_set(v___f_359_, 4, v_toPure_301_);
lean_closure_set(v___f_359_, 5, v_e_284_);
lean_closure_set(v___f_359_, 6, v_value_355_);
v___x_360_ = lean_apply_1(v_g_282_, v_value_355_);
v___x_361_ = lean_apply_4(v_toBind_299_, lean_box(0), lean_box(0), v___x_360_, v___f_359_);
return v___x_361_;
}
case 10:
{
lean_object* v_expr_362_; 
v_expr_362_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_expr_362_);
v_n_303_ = v___x_311_;
v_a_304_ = v_expr_362_;
goto v___jp_302_;
}
default: 
{
lean_dec(v_g_282_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
v_c_286_ = v___x_311_;
v_e_287_ = v_e_284_;
goto v___jp_285_;
}
}
}
}
else
{
lean_dec(v_n_283_);
switch(lean_obj_tag(v_e_284_))
{
case 5:
{
lean_object* v_fn_363_; lean_object* v_arg_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_inc(v_toPure_301_);
lean_inc(v_toBind_299_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
lean_dec_ref(v_inst_278_);
v_fn_363_ = lean_ctor_get(v_e_284_, 0);
lean_inc_ref_n(v_fn_363_, 2);
v_arg_364_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_arg_364_);
v___f_365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_365_, 0, v_arg_364_);
lean_closure_set(v___f_365_, 1, v_toPure_301_);
lean_closure_set(v___f_365_, 2, v_e_284_);
lean_closure_set(v___f_365_, 3, v_fn_363_);
v___x_366_ = lean_apply_1(v_g_282_, v_fn_363_);
v___x_367_ = lean_apply_4(v_toBind_299_, lean_box(0), lean_box(0), v___x_366_, v___f_365_);
return v___x_367_;
}
case 6:
{
lean_object* v_binderName_368_; lean_object* v_binderType_369_; lean_object* v_body_370_; uint8_t v_binderInfo_371_; lean_object* v___x_372_; lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_inc(v_toPure_301_);
lean_inc(v_toBind_299_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
lean_dec_ref(v_inst_278_);
v_binderName_368_ = lean_ctor_get(v_e_284_, 0);
lean_inc(v_binderName_368_);
v_binderType_369_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref_n(v_binderType_369_, 2);
v_body_370_ = lean_ctor_get(v_e_284_, 2);
lean_inc_ref(v_body_370_);
v_binderInfo_371_ = lean_ctor_get_uint8(v_e_284_, sizeof(void*)*3 + 8);
v___x_372_ = lean_box(v_binderInfo_371_);
v___f_373_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed), 7, 6);
lean_closure_set(v___f_373_, 0, v_binderName_368_);
lean_closure_set(v___f_373_, 1, v_body_370_);
lean_closure_set(v___f_373_, 2, v___x_372_);
lean_closure_set(v___f_373_, 3, v_toPure_301_);
lean_closure_set(v___f_373_, 4, v_e_284_);
lean_closure_set(v___f_373_, 5, v_binderType_369_);
v___x_374_ = lean_apply_1(v_g_282_, v_binderType_369_);
v___x_375_ = lean_apply_4(v_toBind_299_, lean_box(0), lean_box(0), v___x_374_, v___f_373_);
return v___x_375_;
}
case 7:
{
lean_object* v_binderName_376_; lean_object* v_binderType_377_; lean_object* v_body_378_; uint8_t v_binderInfo_379_; lean_object* v___x_380_; lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_inc(v_toPure_301_);
lean_inc(v_toBind_299_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
lean_dec_ref(v_inst_278_);
v_binderName_376_ = lean_ctor_get(v_e_284_, 0);
lean_inc(v_binderName_376_);
v_binderType_377_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref_n(v_binderType_377_, 2);
v_body_378_ = lean_ctor_get(v_e_284_, 2);
lean_inc_ref(v_body_378_);
v_binderInfo_379_ = lean_ctor_get_uint8(v_e_284_, sizeof(void*)*3 + 8);
v___x_380_ = lean_box(v_binderInfo_379_);
v___f_381_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_381_, 0, v_binderName_376_);
lean_closure_set(v___f_381_, 1, v_body_378_);
lean_closure_set(v___f_381_, 2, v___x_380_);
lean_closure_set(v___f_381_, 3, v_toPure_301_);
lean_closure_set(v___f_381_, 4, v_e_284_);
lean_closure_set(v___f_381_, 5, v_binderType_377_);
v___x_382_ = lean_apply_1(v_g_282_, v_binderType_377_);
v___x_383_ = lean_apply_4(v_toBind_299_, lean_box(0), lean_box(0), v___x_382_, v___f_381_);
return v___x_383_;
}
case 8:
{
lean_object* v_declName_384_; lean_object* v_type_385_; lean_object* v_value_386_; lean_object* v_body_387_; uint8_t v_nondep_388_; lean_object* v___x_389_; lean_object* v___f_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc(v_toPure_301_);
lean_inc(v_toBind_299_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
lean_dec_ref(v_inst_278_);
v_declName_384_ = lean_ctor_get(v_e_284_, 0);
lean_inc(v_declName_384_);
v_type_385_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref_n(v_type_385_, 2);
v_value_386_ = lean_ctor_get(v_e_284_, 2);
lean_inc_ref(v_value_386_);
v_body_387_ = lean_ctor_get(v_e_284_, 3);
lean_inc_ref(v_body_387_);
v_nondep_388_ = lean_ctor_get_uint8(v_e_284_, sizeof(void*)*4 + 8);
v___x_389_ = lean_box(v_nondep_388_);
v___f_390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed), 8, 7);
lean_closure_set(v___f_390_, 0, v_declName_384_);
lean_closure_set(v___f_390_, 1, v_value_386_);
lean_closure_set(v___f_390_, 2, v_body_387_);
lean_closure_set(v___f_390_, 3, v___x_389_);
lean_closure_set(v___f_390_, 4, v_toPure_301_);
lean_closure_set(v___f_390_, 5, v_e_284_);
lean_closure_set(v___f_390_, 6, v_type_385_);
v___x_391_ = lean_apply_1(v_g_282_, v_type_385_);
v___x_392_ = lean_apply_4(v_toBind_299_, lean_box(0), lean_box(0), v___x_391_, v___f_390_);
return v___x_392_;
}
case 11:
{
lean_object* v_struct_393_; lean_object* v_map_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
lean_inc_ref(v_toFunctor_300_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
lean_dec_ref(v_inst_278_);
v_struct_393_ = lean_ctor_get(v_e_284_, 2);
lean_inc_ref(v_struct_393_);
v_map_394_ = lean_ctor_get(v_toFunctor_300_, 0);
lean_inc(v_map_394_);
lean_dec_ref(v_toFunctor_300_);
v___x_395_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_395_, 0, v_e_284_);
v___x_396_ = lean_apply_1(v_g_282_, v_struct_393_);
v___x_397_ = lean_apply_4(v_map_394_, lean_box(0), lean_box(0), v___x_395_, v___x_396_);
return v___x_397_;
}
case 10:
{
lean_object* v_expr_398_; 
v_expr_398_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_expr_398_);
v_n_303_ = v___x_309_;
v_a_304_ = v_expr_398_;
goto v___jp_302_;
}
default: 
{
lean_dec(v_g_282_);
lean_dec_ref(v_inst_280_);
lean_dec(v_inst_279_);
v_c_286_ = v___x_309_;
v_e_287_ = v_e_284_;
goto v___jp_285_;
}
}
}
v___jp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_288_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1);
v___x_289_ = l_Nat_reprFast(v_c_286_);
v___x_290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = l_Lean_MessageData_ofFormat(v___x_290_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_288_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Lean_MessageData_ofExpr(v_e_287_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_throwError___redArg(v_inst_278_, v_inst_281_, v___x_296_);
return v___x_297_;
}
v___jp_302_:
{
lean_object* v_map_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_map_305_ = lean_ctor_get(v_toFunctor_300_, 0);
lean_inc(v_map_305_);
v___x_306_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_306_, 0, v_e_284_);
v___x_307_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(v_inst_278_, v_inst_279_, v_inst_280_, v_inst_281_, v_g_282_, v_n_303_, v_a_304_);
v___x_308_ = lean_apply_4(v_map_305_, lean_box(0), lean_box(0), v___x_306_, v___x_307_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord(lean_object* v_M_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_g_404_, lean_object* v_n_405_, lean_object* v_e_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(v_inst_400_, v_inst_401_, v_inst_402_, v_inst_403_, v_g_404_, v_n_405_, v_e_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_g_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_413_) == 0)
{
lean_object* v___x_415_; 
lean_dec_ref(v_inst_411_);
lean_dec_ref(v_inst_410_);
lean_dec(v_inst_409_);
lean_dec_ref(v_inst_408_);
v___x_415_ = lean_apply_1(v_g_412_, v_x_414_);
return v___x_415_;
}
else
{
lean_object* v_head_416_; lean_object* v_tail_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_head_416_ = lean_ctor_get(v_x_413_, 0);
lean_inc(v_head_416_);
v_tail_417_ = lean_ctor_get(v_x_413_, 1);
lean_inc(v_tail_417_);
lean_dec_ref(v_x_413_);
lean_inc_ref(v_inst_411_);
lean_inc_ref(v_inst_410_);
lean_inc(v_inst_409_);
lean_inc_ref(v_inst_408_);
v___x_418_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg), 7, 6);
lean_closure_set(v___x_418_, 0, v_inst_408_);
lean_closure_set(v___x_418_, 1, v_inst_409_);
lean_closure_set(v___x_418_, 2, v_inst_410_);
lean_closure_set(v___x_418_, 3, v_inst_411_);
lean_closure_set(v___x_418_, 4, v_g_412_);
lean_closure_set(v___x_418_, 5, v_tail_417_);
v___x_419_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(v_inst_408_, v_inst_409_, v_inst_410_, v_inst_411_, v___x_418_, v_head_416_, v_x_414_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux(lean_object* v_M_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_g_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(v_inst_421_, v_inst_422_, v_inst_423_, v_inst_424_, v_g_425_, v_x_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___redArg(lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_replace_433_, lean_object* v_p_434_, lean_object* v_root_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = l_Lean_SubExpr_Pos_toArray(v_p_434_);
v___x_437_ = lean_array_to_list(v___x_436_);
v___x_438_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(v_inst_429_, v_inst_430_, v_inst_431_, v_inst_432_, v_replace_433_, v___x_437_, v_root_435_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___redArg___boxed(lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_replace_443_, lean_object* v_p_444_, lean_object* v_root_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_replaceSubexpr___redArg(v_inst_439_, v_inst_440_, v_inst_441_, v_inst_442_, v_replace_443_, v_p_444_, v_root_445_);
lean_dec(v_p_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr(lean_object* v_M_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_replace_452_, lean_object* v_p_453_, lean_object* v_root_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Meta_replaceSubexpr___redArg(v_inst_448_, v_inst_449_, v_inst_450_, v_inst_451_, v_replace_452_, v_p_453_, v_root_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___boxed(lean_object* v_M_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_replace_461_, lean_object* v_p_462_, lean_object* v_root_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Meta_replaceSubexpr(v_M_456_, v_inst_457_, v_inst_458_, v_inst_459_, v_inst_460_, v_replace_461_, v_p_462_, v_root_463_);
lean_dec(v_p_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0(lean_object* v_fvars_465_, lean_object* v_k_466_, lean_object* v_body_467_, lean_object* v_x_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_array_push(v_fvars_465_, v_x_468_);
v___x_470_ = lean_apply_2(v_k_466_, v___x_469_, v_body_467_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1(lean_object* v_fvars_471_, lean_object* v_k_472_, lean_object* v_b_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_array_push(v_fvars_471_, v_x_474_);
v___x_476_ = lean_apply_2(v_k_472_, v___x_475_, v_b_473_);
return v___x_476_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_k_483_, lean_object* v_fvars_484_, lean_object* v_n_485_, lean_object* v_e_486_){
_start:
{
lean_object* v_c_488_; lean_object* v_e_489_; lean_object* v_n_501_; lean_object* v_y_502_; lean_object* v_b_503_; uint8_t v_c_504_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(3u);
v___x_510_ = lean_nat_dec_eq(v_n_485_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_nat_dec_eq(v_n_485_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_dec_eq(v_n_485_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(2u);
v___x_516_ = lean_nat_dec_eq(v_n_485_, v___x_515_);
if (v___x_516_ == 0)
{
if (lean_obj_tag(v_e_486_) == 10)
{
lean_object* v_expr_517_; 
v_expr_517_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_expr_517_);
lean_dec_ref(v_e_486_);
v_e_486_ = v_expr_517_;
goto _start;
}
else
{
lean_dec_ref(v_fvars_484_);
lean_dec(v_k_483_);
lean_dec_ref(v_inst_481_);
v_c_488_ = v_n_485_;
v_e_489_ = v_e_486_;
goto v___jp_487_;
}
}
else
{
lean_dec(v_n_485_);
switch(lean_obj_tag(v_e_486_))
{
case 8:
{
lean_object* v_declName_519_; lean_object* v_type_520_; lean_object* v_value_521_; lean_object* v_body_522_; lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; 
lean_dec_ref(v_inst_482_);
v_declName_519_ = lean_ctor_get(v_e_486_, 0);
lean_inc(v_declName_519_);
v_type_520_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_type_520_);
v_value_521_ = lean_ctor_get(v_e_486_, 2);
lean_inc_ref(v_value_521_);
v_body_522_ = lean_ctor_get(v_e_486_, 3);
lean_inc_ref(v_body_522_);
lean_dec_ref(v_e_486_);
lean_inc_ref(v_fvars_484_);
v___f_523_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0), 4, 3);
lean_closure_set(v___f_523_, 0, v_fvars_484_);
lean_closure_set(v___f_523_, 1, v_k_483_);
lean_closure_set(v___f_523_, 2, v_body_522_);
v___x_524_ = lean_expr_instantiate_rev(v_type_520_, v_fvars_484_);
lean_dec_ref(v_type_520_);
v___x_525_ = lean_expr_instantiate_rev(v_value_521_, v_fvars_484_);
lean_dec_ref(v_fvars_484_);
lean_dec_ref(v_value_521_);
v___x_526_ = 0;
v___x_527_ = l_Lean_Meta_withLetDecl___redArg(v_inst_481_, v_inst_480_, v_declName_519_, v___x_524_, v___x_525_, v___f_523_, v___x_514_, v___x_526_);
return v___x_527_;
}
case 10:
{
lean_object* v_expr_528_; 
v_expr_528_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_expr_528_);
lean_dec_ref(v_e_486_);
v_n_485_ = v___x_515_;
v_e_486_ = v_expr_528_;
goto _start;
}
default: 
{
lean_dec_ref(v_fvars_484_);
lean_dec(v_k_483_);
lean_dec_ref(v_inst_481_);
v_c_488_ = v___x_515_;
v_e_489_ = v_e_486_;
goto v___jp_487_;
}
}
}
}
else
{
lean_dec(v_n_485_);
switch(lean_obj_tag(v_e_486_))
{
case 5:
{
lean_object* v_arg_530_; lean_object* v___x_531_; 
lean_dec_ref(v_inst_482_);
lean_dec_ref(v_inst_481_);
lean_dec_ref(v_inst_480_);
v_arg_530_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_arg_530_);
lean_dec_ref(v_e_486_);
v___x_531_ = lean_apply_2(v_k_483_, v_fvars_484_, v_arg_530_);
return v___x_531_;
}
case 6:
{
lean_object* v_binderName_532_; lean_object* v_binderType_533_; lean_object* v_body_534_; uint8_t v_binderInfo_535_; 
lean_dec_ref(v_inst_482_);
v_binderName_532_ = lean_ctor_get(v_e_486_, 0);
lean_inc(v_binderName_532_);
v_binderType_533_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_binderType_533_);
v_body_534_ = lean_ctor_get(v_e_486_, 2);
lean_inc_ref(v_body_534_);
v_binderInfo_535_ = lean_ctor_get_uint8(v_e_486_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_486_);
v_n_501_ = v_binderName_532_;
v_y_502_ = v_binderType_533_;
v_b_503_ = v_body_534_;
v_c_504_ = v_binderInfo_535_;
goto v___jp_500_;
}
case 7:
{
lean_object* v_binderName_536_; lean_object* v_binderType_537_; lean_object* v_body_538_; uint8_t v_binderInfo_539_; 
lean_dec_ref(v_inst_482_);
v_binderName_536_ = lean_ctor_get(v_e_486_, 0);
lean_inc(v_binderName_536_);
v_binderType_537_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_binderType_537_);
v_body_538_ = lean_ctor_get(v_e_486_, 2);
lean_inc_ref(v_body_538_);
v_binderInfo_539_ = lean_ctor_get_uint8(v_e_486_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_486_);
v_n_501_ = v_binderName_536_;
v_y_502_ = v_binderType_537_;
v_b_503_ = v_body_538_;
v_c_504_ = v_binderInfo_539_;
goto v___jp_500_;
}
case 8:
{
lean_object* v_value_540_; lean_object* v___x_541_; 
lean_dec_ref(v_inst_482_);
lean_dec_ref(v_inst_481_);
lean_dec_ref(v_inst_480_);
v_value_540_ = lean_ctor_get(v_e_486_, 2);
lean_inc_ref(v_value_540_);
lean_dec_ref(v_e_486_);
v___x_541_ = lean_apply_2(v_k_483_, v_fvars_484_, v_value_540_);
return v___x_541_;
}
case 10:
{
lean_object* v_expr_542_; 
v_expr_542_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_expr_542_);
lean_dec_ref(v_e_486_);
v_n_485_ = v___x_513_;
v_e_486_ = v_expr_542_;
goto _start;
}
default: 
{
lean_dec_ref(v_fvars_484_);
lean_dec(v_k_483_);
lean_dec_ref(v_inst_481_);
v_c_488_ = v___x_513_;
v_e_489_ = v_e_486_;
goto v___jp_487_;
}
}
}
}
else
{
lean_dec(v_n_485_);
switch(lean_obj_tag(v_e_486_))
{
case 5:
{
lean_object* v_fn_544_; lean_object* v___x_545_; 
lean_dec_ref(v_inst_482_);
lean_dec_ref(v_inst_481_);
lean_dec_ref(v_inst_480_);
v_fn_544_ = lean_ctor_get(v_e_486_, 0);
lean_inc_ref(v_fn_544_);
lean_dec_ref(v_e_486_);
v___x_545_ = lean_apply_2(v_k_483_, v_fvars_484_, v_fn_544_);
return v___x_545_;
}
case 6:
{
lean_object* v_binderType_546_; lean_object* v___x_547_; 
lean_dec_ref(v_inst_482_);
lean_dec_ref(v_inst_481_);
lean_dec_ref(v_inst_480_);
v_binderType_546_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_binderType_546_);
lean_dec_ref(v_e_486_);
v___x_547_ = lean_apply_2(v_k_483_, v_fvars_484_, v_binderType_546_);
return v___x_547_;
}
case 7:
{
lean_object* v_binderType_548_; lean_object* v___x_549_; 
lean_dec_ref(v_inst_482_);
lean_dec_ref(v_inst_481_);
lean_dec_ref(v_inst_480_);
v_binderType_548_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_binderType_548_);
lean_dec_ref(v_e_486_);
v___x_549_ = lean_apply_2(v_k_483_, v_fvars_484_, v_binderType_548_);
return v___x_549_;
}
case 8:
{
lean_object* v_type_550_; lean_object* v___x_551_; 
lean_dec_ref(v_inst_482_);
lean_dec_ref(v_inst_481_);
lean_dec_ref(v_inst_480_);
v_type_550_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_type_550_);
lean_dec_ref(v_e_486_);
v___x_551_ = lean_apply_2(v_k_483_, v_fvars_484_, v_type_550_);
return v___x_551_;
}
case 11:
{
lean_object* v_struct_552_; lean_object* v___x_553_; 
lean_dec_ref(v_inst_482_);
lean_dec_ref(v_inst_481_);
lean_dec_ref(v_inst_480_);
v_struct_552_ = lean_ctor_get(v_e_486_, 2);
lean_inc_ref(v_struct_552_);
lean_dec_ref(v_e_486_);
v___x_553_ = lean_apply_2(v_k_483_, v_fvars_484_, v_struct_552_);
return v___x_553_;
}
case 10:
{
lean_object* v_expr_554_; 
v_expr_554_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_expr_554_);
lean_dec_ref(v_e_486_);
v_n_485_ = v___x_511_;
v_e_486_ = v_expr_554_;
goto _start;
}
default: 
{
lean_dec_ref(v_fvars_484_);
lean_dec(v_k_483_);
lean_dec_ref(v_inst_481_);
v_c_488_ = v___x_511_;
v_e_489_ = v_e_486_;
goto v___jp_487_;
}
}
}
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec_ref(v_e_486_);
lean_dec(v_n_485_);
lean_dec_ref(v_fvars_484_);
lean_dec(v_k_483_);
lean_dec_ref(v_inst_481_);
v___x_556_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1);
v___x_557_ = l_Lean_throwError___redArg(v_inst_480_, v_inst_482_, v___x_556_);
return v___x_557_;
}
v___jp_487_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_490_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1);
v___x_491_ = l_Nat_reprFast(v_c_488_);
v___x_492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
v___x_493_ = l_Lean_MessageData_ofFormat(v___x_492_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_490_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = l_Lean_MessageData_ofExpr(v_e_489_);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_throwError___redArg(v_inst_480_, v_inst_482_, v___x_498_);
return v___x_499_;
}
v___jp_500_:
{
lean_object* v___f_505_; lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; 
lean_inc_ref(v_fvars_484_);
v___f_505_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_505_, 0, v_fvars_484_);
lean_closure_set(v___f_505_, 1, v_k_483_);
lean_closure_set(v___f_505_, 2, v_b_503_);
v___x_506_ = lean_expr_instantiate_rev(v_y_502_, v_fvars_484_);
lean_dec_ref(v_fvars_484_);
lean_dec_ref(v_y_502_);
v___x_507_ = 0;
v___x_508_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_481_, v_inst_480_, v_n_501_, v_c_504_, v___x_506_, v___f_505_, v___x_507_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux(lean_object* v_M_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_00_u03b1_562_, lean_object* v_k_563_, lean_object* v_fvars_564_, lean_object* v_n_565_, lean_object* v_e_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(v_inst_559_, v_inst_560_, v_inst_561_, v_k_563_, v_fvars_564_, v_n_565_, v_e_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(lean_object* v_fvars_568_, lean_object* v_k_569_, lean_object* v_otherFvars_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = l_Array_append___redArg(v_fvars_568_, v_otherFvars_570_);
v___x_573_ = lean_apply_2(v_k_569_, v___x_572_, v___y_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed(lean_object* v_fvars_574_, lean_object* v_k_575_, lean_object* v_otherFvars_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(v_fvars_574_, v_k_575_, v_otherFvars_576_, v___y_577_);
lean_dec_ref(v_otherFvars_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2(lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v___f_585_, lean_object* v_tail_586_, lean_object* v_y_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0));
v___x_589_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(v_inst_581_, v_inst_582_, v_inst_583_, v_inst_584_, v___f_585_, v___x_588_, v_tail_586_, v_y_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_k_594_, lean_object* v_fvars_595_, lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec_ref(v_inst_593_);
lean_dec_ref(v_inst_592_);
lean_dec(v_inst_591_);
lean_dec_ref(v_inst_590_);
v___x_598_ = lean_expr_instantiate_rev(v_x_597_, v_fvars_595_);
lean_dec_ref(v_x_597_);
v___x_599_ = lean_apply_2(v_k_594_, v_fvars_595_, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v_toBind_600_; lean_object* v_head_601_; lean_object* v_tail_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_toBind_600_ = lean_ctor_get(v_inst_590_, 1);
v_head_601_ = lean_ctor_get(v_x_596_, 0);
lean_inc(v_head_601_);
v_tail_602_ = lean_ctor_get(v_x_596_, 1);
lean_inc(v_tail_602_);
lean_dec_ref(v_x_596_);
v___x_603_ = lean_unsigned_to_nat(3u);
v___x_604_ = lean_nat_dec_eq(v_head_601_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___f_605_; lean_object* v___x_606_; 
lean_inc_ref(v_inst_593_);
lean_inc_ref(v_inst_592_);
lean_inc_ref(v_inst_590_);
v___f_605_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0), 8, 6);
lean_closure_set(v___f_605_, 0, v_inst_590_);
lean_closure_set(v___f_605_, 1, v_inst_591_);
lean_closure_set(v___f_605_, 2, v_inst_592_);
lean_closure_set(v___f_605_, 3, v_inst_593_);
lean_closure_set(v___f_605_, 4, v_k_594_);
lean_closure_set(v___f_605_, 5, v_tail_602_);
v___x_606_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(v_inst_590_, v_inst_592_, v_inst_593_, v___f_605_, v_fvars_595_, v_head_601_, v_x_597_);
return v___x_606_;
}
else
{
lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
lean_inc(v_toBind_600_);
lean_dec(v_head_601_);
lean_inc_ref(v_fvars_595_);
v___f_607_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_607_, 0, v_fvars_595_);
lean_closure_set(v___f_607_, 1, v_k_594_);
lean_inc(v_inst_591_);
v___f_608_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2), 7, 6);
lean_closure_set(v___f_608_, 0, v_inst_590_);
lean_closure_set(v___f_608_, 1, v_inst_591_);
lean_closure_set(v___f_608_, 2, v_inst_592_);
lean_closure_set(v___f_608_, 3, v_inst_593_);
lean_closure_set(v___f_608_, 4, v___f_607_);
lean_closure_set(v___f_608_, 5, v_tail_602_);
v___x_609_ = lean_expr_instantiate_rev(v_x_597_, v_fvars_595_);
lean_dec_ref(v_fvars_595_);
lean_dec_ref(v_x_597_);
v___x_610_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_610_, 0, v___x_609_);
v___x_611_ = lean_apply_2(v_inst_591_, lean_box(0), v___x_610_);
v___x_612_ = lean_apply_4(v_toBind_600_, lean_box(0), lean_box(0), v___x_611_, v___f_608_);
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0(lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_k_617_, lean_object* v_tail_618_, lean_object* v_fvars_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(v_inst_613_, v_inst_614_, v_inst_615_, v_inst_616_, v_k_617_, v_fvars_619_, v_tail_618_, v___y_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux(lean_object* v_M_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_00_u03b1_627_, lean_object* v_k_628_, lean_object* v_fvars_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(v_inst_623_, v_inst_624_, v_inst_625_, v_inst_626_, v_k_628_, v_fvars_629_, v_x_630_, v_x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___redArg(lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_visit_637_, lean_object* v_p_638_, lean_object* v_root_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0));
v___x_641_ = l_Lean_SubExpr_Pos_toArray(v_p_638_);
v___x_642_ = lean_array_to_list(v___x_641_);
v___x_643_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(v_inst_633_, v_inst_634_, v_inst_635_, v_inst_636_, v_visit_637_, v___x_640_, v___x_642_, v_root_639_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___redArg___boxed(lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_visit_648_, lean_object* v_p_649_, lean_object* v_root_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_viewSubexpr___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_inst_647_, v_visit_648_, v_p_649_, v_root_650_);
lean_dec(v_p_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr(lean_object* v_M_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_00_u03b1_657_, lean_object* v_visit_658_, lean_object* v_p_659_, lean_object* v_root_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Meta_viewSubexpr___redArg(v_inst_653_, v_inst_654_, v_inst_655_, v_inst_656_, v_visit_658_, v_p_659_, v_root_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___boxed(lean_object* v_M_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_00_u03b1_667_, lean_object* v_visit_668_, lean_object* v_p_669_, lean_object* v_root_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Meta_viewSubexpr(v_M_662_, v_inst_663_, v_inst_664_, v_inst_665_, v_inst_666_, v_00_u03b1_667_, v_visit_668_, v_p_669_, v_root_670_);
lean_dec(v_p_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(lean_object* v_fvars_672_, lean_object* v_k_673_, lean_object* v_otherFvars_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = l_Array_append___redArg(v_fvars_672_, v_otherFvars_674_);
v___x_679_ = lean_apply_4(v_k_673_, v___x_678_, v___y_675_, v___y_676_, v___y_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed(lean_object* v_fvars_680_, lean_object* v_k_681_, lean_object* v_otherFvars_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(v_fvars_680_, v_k_681_, v_otherFvars_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec_ref(v_otherFvars_682_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2(lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v___f_691_, lean_object* v_tail_692_, lean_object* v_y_693_, lean_object* v_acc_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0));
v___x_696_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(v_inst_687_, v_inst_688_, v_inst_689_, v_inst_690_, v___f_691_, v_acc_694_, v_tail_692_, v___x_695_, v_y_693_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3(lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v___f_701_, lean_object* v_tail_702_, lean_object* v_k_703_, lean_object* v_fvars_704_, lean_object* v_current_705_, lean_object* v___x_706_, lean_object* v_acc_707_, lean_object* v_toBind_708_, lean_object* v_y_709_){
_start:
{
lean_object* v___f_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___f_710_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2), 8, 7);
lean_closure_set(v___f_710_, 0, v_inst_697_);
lean_closure_set(v___f_710_, 1, v_inst_698_);
lean_closure_set(v___f_710_, 2, v_inst_699_);
lean_closure_set(v___f_710_, 3, v_inst_700_);
lean_closure_set(v___f_710_, 4, v___f_701_);
lean_closure_set(v___f_710_, 5, v_tail_702_);
lean_closure_set(v___f_710_, 6, v_y_709_);
v___x_711_ = lean_apply_4(v_k_703_, v_fvars_704_, v_current_705_, v___x_706_, v_acc_707_);
v___x_712_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_711_, v___f_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_k_717_, lean_object* v_acc_718_, lean_object* v_address_719_, lean_object* v_fvars_720_, lean_object* v_current_721_){
_start:
{
if (lean_obj_tag(v_address_719_) == 0)
{
lean_object* v_toApplicative_722_; lean_object* v_toPure_723_; lean_object* v___x_724_; 
v_toApplicative_722_ = lean_ctor_get(v_inst_713_, 0);
lean_inc_ref(v_toApplicative_722_);
lean_dec_ref(v_current_721_);
lean_dec_ref(v_fvars_720_);
lean_dec(v_k_717_);
lean_dec_ref(v_inst_716_);
lean_dec_ref(v_inst_715_);
lean_dec(v_inst_714_);
lean_dec_ref(v_inst_713_);
v_toPure_723_ = lean_ctor_get(v_toApplicative_722_, 1);
lean_inc(v_toPure_723_);
lean_dec_ref(v_toApplicative_722_);
v___x_724_ = lean_apply_2(v_toPure_723_, lean_box(0), v_acc_718_);
return v___x_724_;
}
else
{
lean_object* v_toBind_725_; lean_object* v_head_726_; lean_object* v_tail_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v_toBind_725_ = lean_ctor_get(v_inst_713_, 1);
lean_inc(v_toBind_725_);
v_head_726_ = lean_ctor_get(v_address_719_, 0);
lean_inc(v_head_726_);
v_tail_727_ = lean_ctor_get(v_address_719_, 1);
lean_inc(v_tail_727_);
lean_dec_ref(v_address_719_);
v___x_728_ = lean_unsigned_to_nat(3u);
v___x_729_ = lean_nat_dec_eq(v_head_726_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___f_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_inc_ref(v_current_721_);
lean_inc(v_head_726_);
lean_inc_ref(v_fvars_720_);
lean_inc(v_k_717_);
v___f_730_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0), 10, 9);
lean_closure_set(v___f_730_, 0, v_inst_713_);
lean_closure_set(v___f_730_, 1, v_inst_714_);
lean_closure_set(v___f_730_, 2, v_inst_715_);
lean_closure_set(v___f_730_, 3, v_inst_716_);
lean_closure_set(v___f_730_, 4, v_k_717_);
lean_closure_set(v___f_730_, 5, v_tail_727_);
lean_closure_set(v___f_730_, 6, v_fvars_720_);
lean_closure_set(v___f_730_, 7, v_head_726_);
lean_closure_set(v___f_730_, 8, v_current_721_);
v___x_731_ = lean_expr_instantiate_rev(v_current_721_, v_fvars_720_);
lean_dec_ref(v_current_721_);
v___x_732_ = lean_apply_4(v_k_717_, v_fvars_720_, v___x_731_, v_head_726_, v_acc_718_);
v___x_733_ = lean_apply_4(v_toBind_725_, lean_box(0), lean_box(0), v___x_732_, v___f_730_);
return v___x_733_;
}
else
{
lean_object* v___f_734_; lean_object* v_current_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v_head_726_);
lean_inc(v_k_717_);
lean_inc_ref(v_fvars_720_);
v___f_734_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_734_, 0, v_fvars_720_);
lean_closure_set(v___f_734_, 1, v_k_717_);
v_current_735_ = lean_expr_instantiate_rev(v_current_721_, v_fvars_720_);
lean_dec_ref(v_current_721_);
lean_inc(v_toBind_725_);
lean_inc_ref(v_current_735_);
lean_inc(v_inst_714_);
v___f_736_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3), 13, 12);
lean_closure_set(v___f_736_, 0, v_inst_713_);
lean_closure_set(v___f_736_, 1, v_inst_714_);
lean_closure_set(v___f_736_, 2, v_inst_715_);
lean_closure_set(v___f_736_, 3, v_inst_716_);
lean_closure_set(v___f_736_, 4, v___f_734_);
lean_closure_set(v___f_736_, 5, v_tail_727_);
lean_closure_set(v___f_736_, 6, v_k_717_);
lean_closure_set(v___f_736_, 7, v_fvars_720_);
lean_closure_set(v___f_736_, 8, v_current_735_);
lean_closure_set(v___f_736_, 9, v___x_728_);
lean_closure_set(v___f_736_, 10, v_acc_718_);
lean_closure_set(v___f_736_, 11, v_toBind_725_);
v___x_737_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_737_, 0, v_current_735_);
v___x_738_ = lean_apply_2(v_inst_714_, lean_box(0), v___x_737_);
v___x_739_ = lean_apply_4(v_toBind_725_, lean_box(0), lean_box(0), v___x_738_, v___f_736_);
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0(lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_k_744_, lean_object* v_tail_745_, lean_object* v_fvars_746_, lean_object* v_head_747_, lean_object* v_current_748_, lean_object* v_acc_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_inc_ref(v_inst_743_);
lean_inc_ref(v_inst_742_);
lean_inc_ref(v_inst_740_);
v___x_750_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg), 9, 7);
lean_closure_set(v___x_750_, 0, v_inst_740_);
lean_closure_set(v___x_750_, 1, v_inst_741_);
lean_closure_set(v___x_750_, 2, v_inst_742_);
lean_closure_set(v___x_750_, 3, v_inst_743_);
lean_closure_set(v___x_750_, 4, v_k_744_);
lean_closure_set(v___x_750_, 5, v_acc_749_);
lean_closure_set(v___x_750_, 6, v_tail_745_);
v___x_751_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(v_inst_740_, v_inst_742_, v_inst_743_, v___x_750_, v_fvars_746_, v_head_747_, v_current_748_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux(lean_object* v_M_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_00_u03b1_757_, lean_object* v_k_758_, lean_object* v_acc_759_, lean_object* v_address_760_, lean_object* v_fvars_761_, lean_object* v_current_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(v_inst_753_, v_inst_754_, v_inst_755_, v_inst_756_, v_k_758_, v_acc_759_, v_address_760_, v_fvars_761_, v_current_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___redArg(lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_k_768_, lean_object* v_init_769_, lean_object* v_p_770_, lean_object* v_e_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_772_ = l_Lean_SubExpr_Pos_toArray(v_p_770_);
v___x_773_ = lean_array_to_list(v___x_772_);
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0));
v___x_775_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(v_inst_764_, v_inst_765_, v_inst_766_, v_inst_767_, v_k_768_, v_init_769_, v___x_773_, v___x_774_, v_e_771_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___redArg___boxed(lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_k_780_, lean_object* v_init_781_, lean_object* v_p_782_, lean_object* v_e_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Meta_foldAncestors___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_inst_779_, v_k_780_, v_init_781_, v_p_782_, v_e_783_);
lean_dec(v_p_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors(lean_object* v_M_785_, lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_00_u03b1_790_, lean_object* v_k_791_, lean_object* v_init_792_, lean_object* v_p_793_, lean_object* v_e_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Meta_foldAncestors___redArg(v_inst_786_, v_inst_787_, v_inst_788_, v_inst_789_, v_k_791_, v_init_792_, v_p_793_, v_e_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___boxed(lean_object* v_M_796_, lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_00_u03b1_801_, lean_object* v_k_802_, lean_object* v_init_803_, lean_object* v_p_804_, lean_object* v_e_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Meta_foldAncestors(v_M_796_, v_inst_797_, v_inst_798_, v_inst_799_, v_inst_800_, v_00_u03b1_801_, v_k_802_, v_init_803_, v_p_804_, v_e_805_);
lean_dec(v_p_804_);
return v_res_806_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0));
v___x_809_ = l_Lean_stringToMessageData(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_e_815_, lean_object* v_n_816_){
_start:
{
lean_object* v_e_818_; lean_object* v_c_819_; lean_object* v_toApplicative_830_; lean_object* v_toPure_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_toApplicative_830_ = lean_ctor_get(v_inst_813_, 0);
v_toPure_831_ = lean_ctor_get(v_toApplicative_830_, 1);
v___x_832_ = lean_unsigned_to_nat(3u);
v___x_833_ = lean_nat_dec_eq(v_n_816_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_nat_dec_eq(v_n_816_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lean_nat_dec_eq(v_n_816_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_unsigned_to_nat(2u);
v___x_839_ = lean_nat_dec_eq(v_n_816_, v___x_838_);
if (v___x_839_ == 0)
{
if (lean_obj_tag(v_e_815_) == 10)
{
lean_object* v_expr_840_; 
v_expr_840_ = lean_ctor_get(v_e_815_, 1);
lean_inc_ref(v_expr_840_);
lean_dec_ref(v_e_815_);
v_e_815_ = v_expr_840_;
goto _start;
}
else
{
v_e_818_ = v_e_815_;
v_c_819_ = v_n_816_;
goto v___jp_817_;
}
}
else
{
lean_dec(v_n_816_);
switch(lean_obj_tag(v_e_815_))
{
case 8:
{
lean_object* v_body_842_; lean_object* v___x_843_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
v_body_842_ = lean_ctor_get(v_e_815_, 3);
lean_inc_ref(v_body_842_);
lean_dec_ref(v_e_815_);
v___x_843_ = lean_apply_2(v_toPure_831_, lean_box(0), v_body_842_);
return v___x_843_;
}
case 10:
{
lean_object* v_expr_844_; 
v_expr_844_ = lean_ctor_get(v_e_815_, 1);
lean_inc_ref(v_expr_844_);
lean_dec_ref(v_e_815_);
v_e_815_ = v_expr_844_;
v_n_816_ = v___x_838_;
goto _start;
}
default: 
{
v_e_818_ = v_e_815_;
v_c_819_ = v___x_838_;
goto v___jp_817_;
}
}
}
}
else
{
lean_dec(v_n_816_);
switch(lean_obj_tag(v_e_815_))
{
case 5:
{
lean_object* v_arg_846_; lean_object* v___x_847_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
v_arg_846_ = lean_ctor_get(v_e_815_, 1);
lean_inc_ref(v_arg_846_);
lean_dec_ref(v_e_815_);
v___x_847_ = lean_apply_2(v_toPure_831_, lean_box(0), v_arg_846_);
return v___x_847_;
}
case 6:
{
lean_object* v_body_848_; lean_object* v___x_849_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
v_body_848_ = lean_ctor_get(v_e_815_, 2);
lean_inc_ref(v_body_848_);
lean_dec_ref(v_e_815_);
v___x_849_ = lean_apply_2(v_toPure_831_, lean_box(0), v_body_848_);
return v___x_849_;
}
case 7:
{
lean_object* v_body_850_; lean_object* v___x_851_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
v_body_850_ = lean_ctor_get(v_e_815_, 2);
lean_inc_ref(v_body_850_);
lean_dec_ref(v_e_815_);
v___x_851_ = lean_apply_2(v_toPure_831_, lean_box(0), v_body_850_);
return v___x_851_;
}
case 8:
{
lean_object* v_value_852_; lean_object* v___x_853_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
v_value_852_ = lean_ctor_get(v_e_815_, 2);
lean_inc_ref(v_value_852_);
lean_dec_ref(v_e_815_);
v___x_853_ = lean_apply_2(v_toPure_831_, lean_box(0), v_value_852_);
return v___x_853_;
}
case 10:
{
lean_object* v_expr_854_; 
v_expr_854_ = lean_ctor_get(v_e_815_, 1);
lean_inc_ref(v_expr_854_);
lean_dec_ref(v_e_815_);
v_e_815_ = v_expr_854_;
v_n_816_ = v___x_836_;
goto _start;
}
default: 
{
v_e_818_ = v_e_815_;
v_c_819_ = v___x_836_;
goto v___jp_817_;
}
}
}
}
else
{
lean_dec(v_n_816_);
switch(lean_obj_tag(v_e_815_))
{
case 5:
{
lean_object* v_fn_856_; lean_object* v___x_857_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
v_fn_856_ = lean_ctor_get(v_e_815_, 0);
lean_inc_ref(v_fn_856_);
lean_dec_ref(v_e_815_);
v___x_857_ = lean_apply_2(v_toPure_831_, lean_box(0), v_fn_856_);
return v___x_857_;
}
case 6:
{
lean_object* v_binderType_858_; lean_object* v___x_859_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
v_binderType_858_ = lean_ctor_get(v_e_815_, 1);
lean_inc_ref(v_binderType_858_);
lean_dec_ref(v_e_815_);
v___x_859_ = lean_apply_2(v_toPure_831_, lean_box(0), v_binderType_858_);
return v___x_859_;
}
case 7:
{
lean_object* v_binderType_860_; lean_object* v___x_861_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
v_binderType_860_ = lean_ctor_get(v_e_815_, 1);
lean_inc_ref(v_binderType_860_);
lean_dec_ref(v_e_815_);
v___x_861_ = lean_apply_2(v_toPure_831_, lean_box(0), v_binderType_860_);
return v___x_861_;
}
case 8:
{
lean_object* v_type_862_; lean_object* v___x_863_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
v_type_862_ = lean_ctor_get(v_e_815_, 1);
lean_inc_ref(v_type_862_);
lean_dec_ref(v_e_815_);
v___x_863_ = lean_apply_2(v_toPure_831_, lean_box(0), v_type_862_);
return v___x_863_;
}
case 11:
{
lean_object* v_struct_864_; lean_object* v___x_865_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_inst_814_);
lean_dec_ref(v_inst_813_);
v_struct_864_ = lean_ctor_get(v_e_815_, 2);
lean_inc_ref(v_struct_864_);
lean_dec_ref(v_e_815_);
v___x_865_ = lean_apply_2(v_toPure_831_, lean_box(0), v_struct_864_);
return v___x_865_;
}
case 10:
{
lean_object* v_expr_866_; 
v_expr_866_ = lean_ctor_get(v_e_815_, 1);
lean_inc_ref(v_expr_866_);
lean_dec_ref(v_e_815_);
v_e_815_ = v_expr_866_;
v_n_816_ = v___x_834_;
goto _start;
}
default: 
{
v_e_818_ = v_e_815_;
v_c_819_ = v___x_834_;
goto v___jp_817_;
}
}
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec(v_n_816_);
v___x_868_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3, &l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3);
v___x_869_ = l_Lean_MessageData_ofExpr(v_e_815_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_throwError___redArg(v_inst_813_, v_inst_814_, v___x_870_);
return v___x_871_;
}
v___jp_817_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_820_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1, &l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1);
v___x_821_ = l_Nat_reprFast(v_c_819_);
v___x_822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
v___x_823_ = l_Lean_MessageData_ofFormat(v___x_822_);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_820_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_obj_once(&l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3, &l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once, _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = l_Lean_MessageData_ofExpr(v_e_818_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Lean_throwError___redArg(v_inst_813_, v_inst_814_, v___x_828_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw(lean_object* v_M_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_e_875_, lean_object* v_n_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(v_inst_873_, v_inst_874_, v_e_875_, v_n_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewSubexpr___redArg(lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_p_880_, lean_object* v_root_881_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
lean_inc_ref(v_inst_878_);
v___x_882_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw), 5, 3);
lean_closure_set(v___x_882_, 0, lean_box(0));
lean_closure_set(v___x_882_, 1, v_inst_878_);
lean_closure_set(v___x_882_, 2, v_inst_879_);
v___x_883_ = l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_878_, v___x_882_, v_root_881_, v_p_880_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewSubexpr(lean_object* v_M_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_p_887_, lean_object* v_root_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_Core_viewSubexpr___redArg(v_inst_885_, v_inst_886_, v_p_887_, v_root_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
lean_object* v_n_893_; lean_object* v_y_894_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_unsigned_to_nat(1u);
v___x_898_ = lean_nat_dec_eq(v_x_890_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_unsigned_to_nat(2u);
v___x_900_ = lean_nat_dec_eq(v_x_890_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec_ref(v_x_891_);
v___x_901_ = lean_box(0);
return v___x_901_;
}
else
{
if (lean_obj_tag(v_x_891_) == 8)
{
lean_object* v_declName_902_; lean_object* v_type_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_declName_902_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_declName_902_);
v_type_903_ = lean_ctor_get(v_x_891_, 1);
lean_inc_ref(v_type_903_);
lean_dec_ref(v_x_891_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v_declName_902_);
lean_ctor_set(v___x_904_, 1, v_type_903_);
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
else
{
lean_object* v___x_906_; 
lean_dec_ref(v_x_891_);
v___x_906_ = lean_box(0);
return v___x_906_;
}
}
}
else
{
switch(lean_obj_tag(v_x_891_))
{
case 6:
{
lean_object* v_binderName_907_; lean_object* v_binderType_908_; 
v_binderName_907_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_binderName_907_);
v_binderType_908_ = lean_ctor_get(v_x_891_, 1);
lean_inc_ref(v_binderType_908_);
lean_dec_ref(v_x_891_);
v_n_893_ = v_binderName_907_;
v_y_894_ = v_binderType_908_;
goto v___jp_892_;
}
case 7:
{
lean_object* v_binderName_909_; lean_object* v_binderType_910_; 
v_binderName_909_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_binderName_909_);
v_binderType_910_ = lean_ctor_get(v_x_891_, 1);
lean_inc_ref(v_binderType_910_);
lean_dec_ref(v_x_891_);
v_n_893_ = v_binderName_909_;
v_y_894_ = v_binderType_910_;
goto v___jp_892_;
}
default: 
{
lean_object* v___x_911_; 
lean_dec_ref(v_x_891_);
v___x_911_ = lean_box(0);
return v___x_911_;
}
}
}
v___jp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v_n_893_);
lean_ctor_set(v___x_895_, 1, v_y_894_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___boxed(lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(v_x_912_, v_x_913_);
lean_dec(v_x_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__0(lean_object* v_toPure_915_, lean_object* v_c_916_, lean_object* v_snd_917_, lean_object* v_fst_918_, lean_object* v_e_u2082_919_){
_start:
{
lean_object* v___y_921_; lean_object* v___x_924_; 
v___x_924_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(v_c_916_, v_snd_917_);
if (lean_obj_tag(v___x_924_) == 0)
{
v___y_921_ = v_fst_918_;
goto v___jp_920_;
}
else
{
lean_object* v_val_925_; lean_object* v___x_926_; 
v_val_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_val_925_);
lean_dec_ref(v___x_924_);
v___x_926_ = lean_array_push(v_fst_918_, v_val_925_);
v___y_921_ = v___x_926_;
goto v___jp_920_;
}
v___jp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v___y_921_);
lean_ctor_set(v___x_922_, 1, v_e_u2082_919_);
v___x_923_ = lean_apply_2(v_toPure_915_, lean_box(0), v___x_922_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__0___boxed(lean_object* v_toPure_927_, lean_object* v_c_928_, lean_object* v_snd_929_, lean_object* v_fst_930_, lean_object* v_e_u2082_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Core_viewBinders___redArg___lam__0(v_toPure_927_, v_c_928_, v_snd_929_, v_fst_930_, v_e_u2082_931_);
lean_dec(v_c_928_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__1(lean_object* v_toPure_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_toBind_936_, lean_object* v_x_937_, lean_object* v_c_938_){
_start:
{
lean_object* v_fst_939_; lean_object* v_snd_940_; lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_fst_939_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_fst_939_);
v_snd_940_ = lean_ctor_get(v_x_937_, 1);
lean_inc_n(v_snd_940_, 2);
lean_dec_ref(v_x_937_);
lean_inc(v_c_938_);
v___f_941_ = lean_alloc_closure((void*)(l_Lean_Core_viewBinders___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_941_, 0, v_toPure_933_);
lean_closure_set(v___f_941_, 1, v_c_938_);
lean_closure_set(v___f_941_, 2, v_snd_940_);
lean_closure_set(v___f_941_, 3, v_fst_939_);
v___x_942_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(v_inst_934_, v_inst_935_, v_snd_940_, v_c_938_);
v___x_943_ = lean_apply_4(v_toBind_936_, lean_box(0), lean_box(0), v___x_942_, v___f_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__2(lean_object* v_toPure_944_, lean_object* v_____x_945_){
_start:
{
lean_object* v_fst_946_; lean_object* v___x_947_; 
v_fst_946_ = lean_ctor_get(v_____x_945_, 0);
lean_inc(v_fst_946_);
lean_dec_ref(v_____x_945_);
v___x_947_ = lean_apply_2(v_toPure_944_, lean_box(0), v_fst_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg(lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_p_952_, lean_object* v_root_953_){
_start:
{
lean_object* v_toApplicative_954_; lean_object* v_toBind_955_; lean_object* v_toPure_956_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_toApplicative_954_ = lean_ctor_get(v_inst_950_, 0);
v_toBind_955_ = lean_ctor_get(v_inst_950_, 1);
lean_inc_n(v_toBind_955_, 2);
v_toPure_956_ = lean_ctor_get(v_toApplicative_954_, 1);
lean_inc_ref(v_inst_950_);
lean_inc_n(v_toPure_956_, 2);
v___f_957_ = lean_alloc_closure((void*)(l_Lean_Core_viewBinders___redArg___lam__1), 6, 4);
lean_closure_set(v___f_957_, 0, v_toPure_956_);
lean_closure_set(v___f_957_, 1, v_inst_950_);
lean_closure_set(v___f_957_, 2, v_inst_951_);
lean_closure_set(v___f_957_, 3, v_toBind_955_);
v___f_958_ = lean_alloc_closure((void*)(l_Lean_Core_viewBinders___redArg___lam__2), 2, 1);
lean_closure_set(v___f_958_, 0, v_toPure_956_);
v___x_959_ = ((lean_object*)(l_Lean_Core_viewBinders___redArg___closed__0));
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v_root_953_);
v___x_961_ = l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_950_, v___f_957_, v___x_960_, v_p_952_);
v___x_962_ = lean_apply_4(v_toBind_955_, lean_box(0), lean_box(0), v___x_961_, v___f_958_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders(lean_object* v_M_963_, lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_p_966_, lean_object* v_root_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Core_viewBinders___redArg(v_inst_964_, v_inst_965_, v_p_966_, v_root_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_numBinders___redArg(lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v_p_972_, lean_object* v_e_973_){
_start:
{
lean_object* v_toApplicative_974_; lean_object* v_toFunctor_975_; lean_object* v_map_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_toApplicative_974_ = lean_ctor_get(v_inst_970_, 0);
v_toFunctor_975_ = lean_ctor_get(v_toApplicative_974_, 0);
v_map_976_ = lean_ctor_get(v_toFunctor_975_, 0);
lean_inc(v_map_976_);
v___x_977_ = ((lean_object*)(l_Lean_Core_numBinders___redArg___closed__0));
v___x_978_ = l_Lean_Core_viewBinders___redArg(v_inst_970_, v_inst_971_, v_p_972_, v_e_973_);
v___x_979_ = lean_apply_4(v_map_976_, lean_box(0), lean_box(0), v___x_977_, v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_numBinders(lean_object* v_M_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_p_983_, lean_object* v_e_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Core_numBinders___redArg(v_inst_981_, v_inst_982_, v_p_983_, v_e_984_);
return v___x_985_;
}
}
lean_object* runtime_initialize_Lean_SubExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ExprLens(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
