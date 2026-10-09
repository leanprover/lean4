// Lean compiler output
// Module: Lean.Compiler.LCNF.ExpandResetReuse
// Imports: public import Lean.Compiler.LCNF.PassManager import Init.While
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.ExpandResetReuse"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.eraseProjIncFor"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "assertion violation: n > 0 -- 0 incs should not be happening\n      "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.remapSets"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.partitionSelfSets"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unused"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 23, 1, 196, 228, 87, 228, 117)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reuseFailAlloc"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 58, 180, 100, 190, 122, 70, 27)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reusejp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 245, 4, 252, 178, 144, 44, 230)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "assertion violation: n == 1 -- n must be one since `resetToken := reset ...`\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.processResetCont"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isShared"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 21, 27, 150, 131, 176, 68, 226)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "resetjp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 44, 28, 106, 212, 154, 129, 104)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "isSharedCheck"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 46, 40, 117, 142, 84, 34, 112)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expandResetReuse"};
static const lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_expandResetReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 183, 62, 154, 7, 128, 85, 195)}};
static const lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_expandResetReuse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_expandResetReuse;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 164, 249, 156, 95, 195, 57, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ExpandResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 11, 111, 203, 109, 196, 117, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(154, 243, 191, 84, 138, 53, 176, 74)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 105, 247, 180, 77, 138, 39, 85)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 100, 40, 107, 220, 34, 211, 1)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 232, 133, 20, 223, 27, 247, 220)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 148, 15, 20, 202, 87, 70, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 233, 102, 190, 62, 169, 58, 201)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 94, 182, 88, 148, 161, 255, 83)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 201, 67, 31, 121, 57, 98)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 72, 63, 210, 236, 125, 229)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 64, 204, 59, 236, 250, 223, 228)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Array_instInhabited___redArg();
return v___x_4_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(lean_object* v_msg_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_toApplicative_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_49_; 
v___x_11_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_12_ = l_StateRefT_x27_instMonad___redArg(v___x_11_);
v_toApplicative_13_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; 
v_unused_50_ = lean_ctor_get(v___x_12_, 1);
lean_dec(v_unused_50_);
v___x_15_ = v___x_12_;
v_isShared_16_ = v_isSharedCheck_49_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_toApplicative_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_49_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v_toFunctor_17_; lean_object* v_toSeq_18_; lean_object* v_toSeqLeft_19_; lean_object* v_toSeqRight_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_47_; 
v_toFunctor_17_ = lean_ctor_get(v_toApplicative_13_, 0);
v_toSeq_18_ = lean_ctor_get(v_toApplicative_13_, 2);
v_toSeqLeft_19_ = lean_ctor_get(v_toApplicative_13_, 3);
v_toSeqRight_20_ = lean_ctor_get(v_toApplicative_13_, 4);
v_isSharedCheck_47_ = !lean_is_exclusive(v_toApplicative_13_);
if (v_isSharedCheck_47_ == 0)
{
lean_object* v_unused_48_; 
v_unused_48_ = lean_ctor_get(v_toApplicative_13_, 1);
lean_dec(v_unused_48_);
v___x_22_ = v_toApplicative_13_;
v_isShared_23_ = v_isSharedCheck_47_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_toSeqRight_20_);
lean_inc(v_toSeqLeft_19_);
lean_inc(v_toSeq_18_);
lean_inc(v_toFunctor_17_);
lean_dec(v_toApplicative_13_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_47_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___f_31_; lean_object* v___x_33_; 
v___f_24_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_25_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_17_);
v___f_26_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_26_, 0, v_toFunctor_17_);
v___f_27_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_27_, 0, v_toFunctor_17_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___f_26_);
lean_ctor_set(v___x_28_, 1, v___f_27_);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_29_, 0, v_toSeqRight_20_);
v___f_30_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_30_, 0, v_toSeqLeft_19_);
v___f_31_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_31_, 0, v_toSeq_18_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 4, v___f_29_);
lean_ctor_set(v___x_22_, 3, v___f_30_);
lean_ctor_set(v___x_22_, 2, v___f_31_);
lean_ctor_set(v___x_22_, 1, v___f_24_);
lean_ctor_set(v___x_22_, 0, v___x_28_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___f_24_);
lean_ctor_set(v_reuseFailAlloc_46_, 2, v___f_31_);
lean_ctor_set(v_reuseFailAlloc_46_, 3, v___f_30_);
lean_ctor_set(v_reuseFailAlloc_46_, 4, v___f_29_);
v___x_33_ = v_reuseFailAlloc_46_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_35_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v___f_25_);
lean_ctor_set(v___x_15_, 0, v___x_33_);
v___x_35_ = v___x_15_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___f_25_);
v___x_35_ = v_reuseFailAlloc_45_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_2594__overap_43_; lean_object* v___x_44_; 
v___x_36_ = l_StateRefT_x27_instMonad___redArg(v___x_35_);
v___x_37_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_37_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
v___x_41_ = l_instInhabitedOfMonad___redArg(v___x_36_, v___x_40_);
v___f_42_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_42_, 0, v___x_41_);
v___x_2594__overap_43_ = lean_panic_fn_borrowed(v___f_42_, v_msg_5_);
lean_dec_ref(v___f_42_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
v___x_44_ = lean_apply_5(v___x_2594__overap_43_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_5_ = stack[0].m_obj;
lean_object* v___y_6_ = stack[1].m_obj;
lean_object* v___y_7_ = stack[2].m_obj;
lean_object* v___y_8_ = stack[3].m_obj;
lean_object* v___y_9_ = stack[4].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v_msg_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___boxed(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v_msg_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_58_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(lean_object* v_fst_59_, lean_object* v_snd_60_, lean_object* v_fst_61_, lean_object* v_x_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v_fst_59_);
lean_ctor_set(v___x_68_, 1, v_snd_60_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v_fst_61_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_59_ = stack[0].m_obj;
lean_object* v_snd_60_ = stack[1].m_obj;
lean_object* v_fst_61_ = stack[2].m_obj;
lean_object* v_x_62_ = stack[3].m_obj;
lean_object* v___y_63_ = stack[4].m_obj;
lean_object* v___y_64_ = stack[5].m_obj;
lean_object* v___y_65_ = stack[6].m_obj;
lean_object* v___y_66_ = stack[7].m_obj;
lean_object* v_res_72_;
v_res_72_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_59_, v_snd_60_, v_fst_61_, v_x_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0___boxed(lean_object* v_fst_73_, lean_object* v_snd_74_, lean_object* v_fst_75_, lean_object* v_x_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_73_, v_snd_74_, v_fst_75_, v_x_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec_ref(v_x_76_);
return v_res_82_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_83_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_87_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3));
v___x_88_ = lean_unsigned_to_nat(6u);
v___x_89_ = lean_unsigned_to_nat(87u);
v___x_90_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2));
v___x_91_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_92_ = l_mkPanicMessageWithDecl(v___x_91_, v___x_90_, v___x_89_, v___x_88_, v___x_87_);
return v___x_92_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(lean_object* v_targetId_93_, lean_object* v_a_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_108_; lean_object* v_snd_128_; lean_object* v_fst_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_271_; 
v_snd_128_ = lean_ctor_get(v_a_94_, 1);
v_fst_129_ = lean_ctor_get(v_a_94_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v_a_94_);
if (v_isSharedCheck_271_ == 0)
{
v___x_131_ = v_a_94_;
v_isShared_132_ = v_isSharedCheck_271_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_snd_128_);
lean_inc(v_fst_129_);
lean_dec(v_a_94_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_271_;
goto v_resetjp_130_;
}
v___jp_100_:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___y_103_);
lean_ctor_set(v___x_104_, 1, v___y_102_);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v___y_101_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v_a_94_ = v___x_105_;
goto _start;
}
v___jp_107_:
{
if (lean_obj_tag(v___y_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_119_; 
v_a_109_ = lean_ctor_get(v___y_108_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___y_108_);
if (v_isSharedCheck_119_ == 0)
{
v___x_111_ = v___y_108_;
v_isShared_112_ = v_isSharedCheck_119_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___y_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_119_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
if (lean_obj_tag(v_a_109_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_115_; 
v_a_113_ = lean_ctor_get(v_a_109_, 0);
lean_inc(v_a_113_);
lean_dec_ref_known(v_a_109_, 1);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v_a_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
else
{
lean_object* v_a_117_; 
lean_del_object(v___x_111_);
v_a_117_ = lean_ctor_get(v_a_109_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v_a_109_, 1);
v_a_94_ = v_a_117_;
goto _start;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___y_108_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___y_108_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___y_108_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___y_108_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
v_resetjp_130_:
{
lean_object* v_fst_133_; lean_object* v_snd_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_270_; 
v_fst_133_ = lean_ctor_get(v_snd_128_, 0);
v_snd_134_ = lean_ctor_get(v_snd_128_, 1);
v_isSharedCheck_270_ = !lean_is_exclusive(v_snd_128_);
if (v_isSharedCheck_270_ == 0)
{
v___x_136_ = v_snd_128_;
v_isShared_137_ = v_isSharedCheck_270_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_snd_134_);
lean_inc(v_fst_133_);
lean_dec(v_snd_128_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_270_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_138_ = lean_unsigned_to_nat(2u);
v___x_139_ = lean_array_get_size(v_fst_129_);
v___x_140_ = lean_nat_dec_le(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_142_; 
if (v_isShared_137_ == 0)
{
v___x_142_ = v___x_136_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_fst_133_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_snd_134_);
v___x_142_ = v_reuseFailAlloc_147_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_142_);
v___x_144_ = v___x_131_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_fst_129_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; 
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_148_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = lean_nat_sub(v___x_139_, v___x_149_);
v___x_151_ = lean_array_get(v___x_148_, v_fst_129_, v___x_150_);
lean_dec(v___x_150_);
switch(lean_obj_tag(v___x_151_))
{
case 0:
{
lean_object* v_decl_152_; lean_object* v_value_153_; 
v_decl_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_ref(v_decl_152_);
v_value_153_ = lean_ctor_get(v_decl_152_, 3);
lean_inc(v_value_153_);
switch(lean_obj_tag(v_value_153_))
{
case 8:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
lean_dec_ref_known(v_value_153_, 3);
lean_dec_ref(v_decl_152_);
v___x_154_ = lean_array_pop(v_fst_129_);
v___x_155_ = lean_array_push(v_fst_133_, v___x_151_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_155_);
v___x_157_ = v___x_136_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_snd_134_);
v___x_157_ = v_reuseFailAlloc_162_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_159_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_157_);
lean_ctor_set(v___x_131_, 0, v___x_154_);
v___x_159_ = v___x_131_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___x_157_);
v___x_159_ = v_reuseFailAlloc_161_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
v_a_94_ = v___x_159_;
goto _start;
}
}
}
case 7:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec_ref_known(v_value_153_, 2);
lean_dec_ref(v_decl_152_);
v___x_163_ = lean_array_pop(v_fst_129_);
v___x_164_ = lean_array_push(v_fst_133_, v___x_151_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_164_);
v___x_166_ = v___x_136_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_snd_134_);
v___x_166_ = v_reuseFailAlloc_171_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_166_);
lean_ctor_set(v___x_131_, 0, v___x_163_);
v___x_168_ = v___x_131_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_170_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
v_a_94_ = v___x_168_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_190_; 
lean_del_object(v___x_136_);
lean_del_object(v___x_131_);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; 
v_unused_191_ = lean_ctor_get(v___x_151_, 0);
lean_dec(v_unused_191_);
v___x_173_ = v___x_151_;
v_isShared_174_ = v_isSharedCheck_190_;
goto v_resetjp_172_;
}
else
{
lean_dec(v___x_151_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_190_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v_fvarId_175_; lean_object* v_binderName_176_; lean_object* v_type_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_188_; 
v_fvarId_175_ = lean_ctor_get(v_decl_152_, 0);
v_binderName_176_ = lean_ctor_get(v_decl_152_, 1);
v_type_177_ = lean_ctor_get(v_decl_152_, 2);
v_isSharedCheck_188_ = !lean_is_exclusive(v_decl_152_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; 
v_unused_189_ = lean_ctor_get(v_decl_152_, 3);
lean_dec(v_unused_189_);
v___x_179_ = v_decl_152_;
v_isShared_180_ = v_isSharedCheck_188_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_type_177_);
lean_inc(v_binderName_176_);
lean_inc(v_fvarId_175_);
lean_dec(v_decl_152_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_188_;
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
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_fvarId_175_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_binderName_176_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_type_177_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_value_153_);
v___x_182_ = v_reuseFailAlloc_187_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_182_);
v___x_184_ = v___x_173_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_186_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; 
v___x_185_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_133_, v_snd_134_, v_fst_129_, v___x_184_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec_ref(v___x_184_);
v___y_108_ = v___x_185_;
goto v___jp_107_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_192_; lean_object* v_n_193_; uint8_t v_check_194_; uint8_t v_persistent_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_fvarId_192_ = lean_ctor_get(v___x_151_, 0);
v_n_193_ = lean_ctor_get(v___x_151_, 1);
v_check_194_ = lean_ctor_get_uint8(v___x_151_, sizeof(void*)*2);
v_persistent_195_ = lean_ctor_get_uint8(v___x_151_, sizeof(void*)*2 + 1);
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_nat_dec_lt(v___x_196_, v_n_193_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec_ref_known(v___x_151_, 2);
lean_del_object(v___x_136_);
lean_dec(v_snd_134_);
lean_dec(v_fst_133_);
lean_del_object(v___x_131_);
lean_dec(v_fst_129_);
v___x_198_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4);
v___x_199_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v___x_198_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
v___y_108_ = v___x_199_;
goto v___jp_107_;
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_nat_sub(v___x_139_, v___x_138_);
v___x_201_ = lean_array_get(v___x_148_, v_fst_129_, v___x_200_);
lean_dec(v___x_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_decl_202_; lean_object* v_value_203_; 
v_decl_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc_ref(v_decl_202_);
v_value_203_ = lean_ctor_get(v_decl_202_, 3);
lean_inc(v_value_203_);
if (lean_obj_tag(v_value_203_) == 6)
{
lean_object* v_fvarId_204_; lean_object* v_i_205_; lean_object* v_var_206_; lean_object* v___x_207_; uint8_t v___y_209_; uint8_t v___x_246_; 
v_fvarId_204_ = lean_ctor_get(v_decl_202_, 0);
lean_inc(v_fvarId_204_);
lean_dec_ref(v_decl_202_);
v_i_205_ = lean_ctor_get(v_value_203_, 0);
lean_inc(v_i_205_);
v_var_206_ = lean_ctor_get(v_value_203_, 1);
lean_inc(v_var_206_);
lean_dec_ref_known(v_value_203_, 2);
v___x_207_ = lean_box(0);
v___x_246_ = l_Lean_instBEqFVarId_beq(v_fvarId_204_, v_fvarId_192_);
lean_dec(v_fvarId_204_);
if (v___x_246_ == 0)
{
lean_dec(v_var_206_);
v___y_209_ = v___x_246_;
goto v___jp_208_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = l_Lean_instBEqFVarId_beq(v_targetId_93_, v_var_206_);
lean_dec(v_var_206_);
v___y_209_ = v___x_247_;
goto v___jp_208_;
}
v___jp_208_:
{
if (v___y_209_ == 0)
{
lean_object* v___x_211_; 
lean_dec(v_i_205_);
lean_dec_ref_known(v___x_201_, 1);
lean_dec_ref_known(v___x_151_, 2);
if (v_isShared_137_ == 0)
{
v___x_211_ = v___x_136_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_fst_133_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_snd_134_);
v___x_211_ = v_reuseFailAlloc_216_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_213_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_211_);
v___x_213_ = v___x_131_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_fst_129_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_211_);
v___x_213_ = v_reuseFailAlloc_215_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; 
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_array_get_borrowed(v___x_207_, v_snd_134_, v_i_205_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_232_; 
lean_inc(v_n_193_);
lean_inc(v_fvarId_192_);
lean_del_object(v___x_136_);
lean_del_object(v___x_131_);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_233_ = lean_ctor_get(v___x_151_, 1);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v___x_151_, 0);
lean_dec(v_unused_234_);
v___x_219_ = v___x_151_;
v_isShared_220_ = v_isSharedCheck_232_;
goto v_resetjp_218_;
}
else
{
lean_dec(v___x_151_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_232_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_221_ = lean_array_pop(v_fst_129_);
v___x_222_ = lean_array_pop(v___x_221_);
lean_inc(v_fvarId_192_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_fvarId_192_);
v___x_224_ = lean_array_set(v_snd_134_, v_i_205_, v___x_223_);
lean_dec(v_i_205_);
v___x_225_ = lean_array_push(v_fst_133_, v___x_201_);
v___x_226_ = lean_nat_dec_eq(v_n_193_, v___x_149_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_nat_sub(v_n_193_, v___x_149_);
lean_dec(v_n_193_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_227_);
v___x_229_ = v___x_219_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_fvarId_192_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_227_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*2, v_check_194_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*2 + 1, v_persistent_195_);
v___x_229_ = v_reuseFailAlloc_231_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; 
v___x_230_ = lean_array_push(v___x_225_, v___x_229_);
v___y_101_ = v___x_222_;
v___y_102_ = v___x_224_;
v___y_103_ = v___x_230_;
goto v___jp_100_;
}
}
else
{
lean_del_object(v___x_219_);
lean_dec(v_n_193_);
lean_dec(v_fvarId_192_);
v___y_101_ = v___x_222_;
v___y_102_ = v___x_224_;
v___y_103_ = v___x_225_;
goto v___jp_100_;
}
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
lean_dec(v_i_205_);
v___x_235_ = lean_array_push(v_fst_133_, v___x_151_);
v___x_236_ = lean_array_push(v___x_235_, v___x_201_);
v___x_237_ = lean_array_pop(v_fst_129_);
v___x_238_ = lean_array_pop(v___x_237_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_236_);
v___x_240_ = v___x_136_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_snd_134_);
v___x_240_ = v_reuseFailAlloc_245_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_240_);
lean_ctor_set(v___x_131_, 0, v___x_238_);
v___x_242_ = v___x_131_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
v_a_94_ = v___x_242_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_266_; 
lean_dec_ref_known(v___x_151_, 2);
lean_del_object(v___x_136_);
lean_del_object(v___x_131_);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v___x_201_, 0);
lean_dec(v_unused_267_);
v___x_249_ = v___x_201_;
v_isShared_250_ = v_isSharedCheck_266_;
goto v_resetjp_248_;
}
else
{
lean_dec(v___x_201_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_266_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_fvarId_251_; lean_object* v_binderName_252_; lean_object* v_type_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_264_; 
v_fvarId_251_ = lean_ctor_get(v_decl_202_, 0);
v_binderName_252_ = lean_ctor_get(v_decl_202_, 1);
v_type_253_ = lean_ctor_get(v_decl_202_, 2);
v_isSharedCheck_264_ = !lean_is_exclusive(v_decl_202_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; 
v_unused_265_ = lean_ctor_get(v_decl_202_, 3);
lean_dec(v_unused_265_);
v___x_255_ = v_decl_202_;
v_isShared_256_ = v_isSharedCheck_264_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_type_253_);
lean_inc(v_binderName_252_);
lean_inc(v_fvarId_251_);
lean_dec(v_decl_202_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_264_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_fvarId_251_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_binderName_252_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_type_253_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v_value_203_);
v___x_258_ = v_reuseFailAlloc_263_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_258_);
v___x_260_ = v___x_249_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_262_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; 
v___x_261_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_133_, v_snd_134_, v_fst_129_, v___x_260_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec_ref(v___x_260_);
v___y_108_ = v___x_261_;
goto v___jp_107_;
}
}
}
}
}
}
else
{
lean_object* v___x_268_; 
lean_dec_ref_known(v___x_151_, 2);
lean_del_object(v___x_136_);
lean_del_object(v___x_131_);
v___x_268_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_133_, v_snd_134_, v_fst_129_, v___x_201_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___x_201_);
v___y_108_ = v___x_268_;
goto v___jp_107_;
}
}
}
default: 
{
lean_object* v___x_269_; 
lean_del_object(v___x_136_);
lean_del_object(v___x_131_);
v___x_269_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_133_, v_snd_134_, v_fst_129_, v___x_151_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___x_151_);
v___y_108_ = v___x_269_;
goto v___jp_107_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetId_93_ = stack[0].m_obj;
lean_object* v_a_94_ = stack[1].m_obj;
lean_object* v___y_95_ = stack[2].m_obj;
lean_object* v___y_96_ = stack[3].m_obj;
lean_object* v___y_97_ = stack[4].m_obj;
lean_object* v___y_98_ = stack[5].m_obj;
lean_object* v_res_272_;
v_res_272_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_93_, v_a_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(lean_object* v_targetId_273_, lean_object* v_a_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_273_, v_a_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v_targetId_273_);
return v_res_280_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object* v_nFields_283_, lean_object* v_targetId_284_, lean_object* v_ds_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_keep_291_; lean_object* v___x_292_; lean_object* v_mask_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_keep_291_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_292_ = lean_box(0);
v_mask_293_ = lean_mk_array(v_nFields_283_, v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_keep_291_);
lean_ctor_set(v___x_294_, 1, v_mask_293_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v_ds_285_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_284_, v___x_295_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_317_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_317_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_317_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_317_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_snd_301_; lean_object* v_fst_302_; lean_object* v_fst_303_; lean_object* v_snd_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_316_; 
v_snd_301_ = lean_ctor_get(v_a_297_, 1);
lean_inc(v_snd_301_);
v_fst_302_ = lean_ctor_get(v_a_297_, 0);
lean_inc(v_fst_302_);
lean_dec(v_a_297_);
v_fst_303_ = lean_ctor_get(v_snd_301_, 0);
v_snd_304_ = lean_ctor_get(v_snd_301_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_snd_301_);
if (v_isSharedCheck_316_ == 0)
{
v___x_306_ = v_snd_301_;
v_isShared_307_ = v_isSharedCheck_316_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_snd_304_);
lean_inc(v_fst_303_);
lean_dec(v_snd_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_316_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = l_Array_reverse___redArg(v_fst_303_);
v___x_309_ = l_Array_append___redArg(v_fst_302_, v___x_308_);
lean_dec_ref(v___x_308_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_309_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_snd_304_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_311_);
v___x_313_ = v___x_299_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
v_a_318_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_296_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_296_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_0interp(lean_interpreter_value* stack)
{
lean_object* v_nFields_283_ = stack[0].m_obj;
lean_object* v_targetId_284_ = stack[1].m_obj;
lean_object* v_ds_285_ = stack[2].m_obj;
lean_object* v_a_286_ = stack[3].m_obj;
lean_object* v_a_287_ = stack[4].m_obj;
lean_object* v_a_288_ = stack[5].m_obj;
lean_object* v_a_289_ = stack[6].m_obj;
lean_object* v_res_326_;
v_res_326_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_283_, v_targetId_284_, v_ds_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
stack->m_obj
 = v_res_326_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object* v_nFields_327_, lean_object* v_targetId_328_, lean_object* v_ds_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_327_, v_targetId_328_, v_ds_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_targetId_328_);
return v_res_335_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object* v_targetId_336_, lean_object* v_inst_337_, lean_object* v_a_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_336_, v_a_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
return v___x_344_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetId_336_ = stack[0].m_obj;
lean_object* v_a_338_ = stack[2].m_obj;
lean_object* v___y_339_ = stack[3].m_obj;
lean_object* v___y_340_ = stack[4].m_obj;
lean_object* v___y_341_ = stack[5].m_obj;
lean_object* v___y_342_ = stack[6].m_obj;
lean_object* v_res_345_;
v_res_345_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(v_targetId_336_, lean_box(0), v_a_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object* v_targetId_346_, lean_object* v_inst_347_, lean_object* v_a_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(v_targetId_346_, v_inst_347_, v_a_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v_targetId_346_);
return v_res_354_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object* v_discr_371_, lean_object* v_discrType_372_, lean_object* v_resultType_373_, lean_object* v_t_374_, lean_object* v_e_375_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_377_ = l_Lean_Expr_getAppFn(v_discrType_372_);
v___x_378_ = l_Lean_Expr_constName_x21(v___x_377_);
lean_dec_ref(v___x_377_);
v___x_379_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3));
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v_e_375_);
v___x_381_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6));
v___x_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_t_374_);
v___x_383_ = lean_unsigned_to_nat(2u);
v___x_384_ = lean_mk_empty_array_with_capacity(v___x_383_);
v___x_385_ = lean_array_push(v___x_384_, v___x_380_);
v___x_386_ = lean_array_push(v___x_385_, v___x_382_);
v___x_387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_387_, 0, v___x_378_);
lean_ctor_set(v___x_387_, 1, v_resultType_373_);
lean_ctor_set(v___x_387_, 2, v_discr_371_);
lean_ctor_set(v___x_387_, 3, v___x_386_);
v___x_388_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_371_ = stack[0].m_obj;
lean_object* v_discrType_372_ = stack[1].m_obj;
lean_object* v_resultType_373_ = stack[2].m_obj;
lean_object* v_t_374_ = stack[3].m_obj;
lean_object* v_e_375_ = stack[4].m_obj;
lean_object* v_res_390_;
v_res_390_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_371_, v_discrType_372_, v_resultType_373_, v_t_374_, v_e_375_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object* v_discr_391_, lean_object* v_discrType_392_, lean_object* v_resultType_393_, lean_object* v_t_394_, lean_object* v_e_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_391_, v_discrType_392_, v_resultType_393_, v_t_394_, v_e_395_);
lean_dec_ref(v_discrType_392_);
return v_res_397_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object* v_discr_398_, lean_object* v_discrType_399_, lean_object* v_resultType_400_, lean_object* v_t_401_, lean_object* v_e_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_398_, v_discrType_399_, v_resultType_400_, v_t_401_, v_e_402_);
return v___x_408_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_398_ = stack[0].m_obj;
lean_object* v_discrType_399_ = stack[1].m_obj;
lean_object* v_resultType_400_ = stack[2].m_obj;
lean_object* v_t_401_ = stack[3].m_obj;
lean_object* v_e_402_ = stack[4].m_obj;
lean_object* v_a_403_ = stack[5].m_obj;
lean_object* v_a_404_ = stack[6].m_obj;
lean_object* v_a_405_ = stack[7].m_obj;
lean_object* v_a_406_ = stack[8].m_obj;
lean_object* v_res_409_;
v_res_409_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(v_discr_398_, v_discrType_399_, v_resultType_400_, v_t_401_, v_e_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object* v_discr_410_, lean_object* v_discrType_411_, lean_object* v_resultType_412_, lean_object* v_t_413_, lean_object* v_e_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(v_discr_410_, v_discrType_411_, v_resultType_412_, v_t_413_, v_e_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec_ref(v_discrType_411_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object* v_msg_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_423_ = lean_panic_fn_borrowed(v___x_422_, v_msg_421_);
return v___x_423_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_427_ = lean_unsigned_to_nat(11u);
v___x_428_ = lean_unsigned_to_nat(138u);
v___x_429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0));
v___x_430_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_431_ = l_mkPanicMessageWithDecl(v___x_430_, v___x_429_, v___x_428_, v___x_427_, v___x_426_);
return v___x_431_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object* v_targetId_432_, size_t v_sz_433_, size_t v_i_434_, lean_object* v_bs_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_lt(v_i_434_, v_sz_433_);
if (v___x_436_ == 0)
{
lean_dec(v_targetId_432_);
return v_bs_435_;
}
else
{
lean_object* v_v_437_; lean_object* v___x_438_; lean_object* v_bs_x27_439_; lean_object* v___y_441_; 
v_v_437_ = lean_array_uget(v_bs_435_, v_i_434_);
v___x_438_ = lean_unsigned_to_nat(0u);
v_bs_x27_439_ = lean_array_uset(v_bs_435_, v_i_434_, v___x_438_);
switch(lean_obj_tag(v_v_437_))
{
case 3:
{
lean_object* v_i_446_; lean_object* v_y_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_i_446_ = lean_ctor_get(v_v_437_, 1);
v_y_447_ = lean_ctor_get(v_v_437_, 2);
v_isSharedCheck_454_ = !lean_is_exclusive(v_v_437_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v_v_437_, 0);
lean_dec(v_unused_455_);
v___x_449_ = v_v_437_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_y_447_);
lean_inc(v_i_446_);
lean_dec(v_v_437_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
lean_inc(v_targetId_432_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v_targetId_432_);
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_targetId_432_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_i_446_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_y_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
v___y_441_ = v___x_452_;
goto v___jp_440_;
}
}
}
case 5:
{
lean_object* v_i_456_; lean_object* v_offset_457_; lean_object* v_y_458_; lean_object* v_ty_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_i_456_ = lean_ctor_get(v_v_437_, 1);
v_offset_457_ = lean_ctor_get(v_v_437_, 2);
v_y_458_ = lean_ctor_get(v_v_437_, 3);
v_ty_459_ = lean_ctor_get(v_v_437_, 4);
v_isSharedCheck_466_ = !lean_is_exclusive(v_v_437_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v_v_437_, 0);
lean_dec(v_unused_467_);
v___x_461_ = v_v_437_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_ty_459_);
lean_inc(v_y_458_);
lean_inc(v_offset_457_);
lean_inc(v_i_456_);
lean_dec(v_v_437_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
lean_inc(v_targetId_432_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v_targetId_432_);
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_targetId_432_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_i_456_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_offset_457_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_y_458_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_ty_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
v___y_441_ = v___x_464_;
goto v___jp_440_;
}
}
}
case 4:
{
lean_object* v_i_468_; lean_object* v_y_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
v_i_468_ = lean_ctor_get(v_v_437_, 1);
v_y_469_ = lean_ctor_get(v_v_437_, 2);
v_isSharedCheck_476_ = !lean_is_exclusive(v_v_437_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; 
v_unused_477_ = lean_ctor_get(v_v_437_, 0);
lean_dec(v_unused_477_);
v___x_471_ = v_v_437_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_y_469_);
lean_inc(v_i_468_);
lean_dec(v_v_437_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
lean_inc(v_targetId_432_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v_targetId_432_);
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_targetId_432_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_i_468_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_y_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
v___y_441_ = v___x_474_;
goto v___jp_440_;
}
}
}
default: 
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_v_437_);
v___x_478_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2);
v___x_479_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(v___x_478_);
v___y_441_ = v___x_479_;
goto v___jp_440_;
}
}
v___jp_440_:
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_add(v_i_434_, v___x_442_);
v___x_444_ = lean_array_uset(v_bs_x27_439_, v_i_434_, v___y_441_);
v_i_434_ = v___x_443_;
v_bs_435_ = v___x_444_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetId_432_ = stack[0].m_obj;
size_t v_sz_433_ = stack[1].m_num;
size_t v_i_434_ = stack[2].m_num;
lean_object* v_bs_435_ = stack[3].m_obj;
lean_object* v_res_480_;
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_432_, v_sz_433_, v_i_434_, v_bs_435_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object* v_targetId_481_, lean_object* v_sz_482_, lean_object* v_i_483_, lean_object* v_bs_484_){
_start:
{
size_t v_sz_boxed_485_; size_t v_i_boxed_486_; lean_object* v_res_487_; 
v_sz_boxed_485_ = lean_unbox_usize(v_sz_482_);
lean_dec(v_sz_482_);
v_i_boxed_486_ = lean_unbox_usize(v_i_483_);
lean_dec(v_i_483_);
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_481_, v_sz_boxed_485_, v_i_boxed_486_, v_bs_484_);
return v_res_487_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object* v_targetId_488_, lean_object* v_sets_489_){
_start:
{
size_t v_sz_491_; size_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_sz_491_ = lean_array_size(v_sets_489_);
v___x_492_ = ((size_t)0ULL);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_488_, v_sz_491_, v___x_492_, v_sets_489_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetId_488_ = stack[0].m_obj;
lean_object* v_sets_489_ = stack[1].m_obj;
lean_object* v_res_495_;
v_res_495_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_488_, v_sets_489_);
stack->m_obj
 = v_res_495_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object* v_targetId_496_, lean_object* v_sets_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_496_, v_sets_497_);
return v_res_499_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object* v_targetId_500_, lean_object* v_sets_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_500_, v_sets_501_);
return v___x_507_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetId_500_ = stack[0].m_obj;
lean_object* v_sets_501_ = stack[1].m_obj;
lean_object* v_a_502_ = stack[2].m_obj;
lean_object* v_a_503_ = stack[3].m_obj;
lean_object* v_a_504_ = stack[4].m_obj;
lean_object* v_a_505_ = stack[5].m_obj;
lean_object* v_res_508_;
v_res_508_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(v_targetId_500_, v_sets_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object* v_targetId_509_, lean_object* v_sets_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(v_targetId_509_, v_sets_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
return v_res_516_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object* v_fvarId_517_, lean_object* v_i_518_, lean_object* v_y_519_, lean_object* v_a_520_){
_start:
{
if (lean_obj_tag(v_y_519_) == 0)
{
uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = 0;
v___x_523_ = lean_box(v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
else
{
lean_object* v_fvarId_525_; uint8_t v___x_526_; lean_object* v___x_527_; 
v_fvarId_525_ = lean_ctor_get(v_y_519_, 0);
v___x_526_ = 1;
v___x_527_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_526_, v_fvarId_525_, v_a_520_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_555_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_555_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_555_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_555_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
if (lean_obj_tag(v_a_528_) == 1)
{
lean_object* v_val_532_; 
v_val_532_ = lean_ctor_get(v_a_528_, 0);
lean_inc(v_val_532_);
lean_dec_ref_known(v_a_528_, 1);
if (lean_obj_tag(v_val_532_) == 6)
{
lean_object* v_i_533_; lean_object* v_var_534_; uint8_t v___x_535_; 
v_i_533_ = lean_ctor_get(v_val_532_, 0);
lean_inc(v_i_533_);
v_var_534_ = lean_ctor_get(v_val_532_, 1);
lean_inc(v_var_534_);
lean_dec_ref_known(v_val_532_, 2);
v___x_535_ = lean_nat_dec_eq(v_i_518_, v_i_533_);
lean_dec(v_i_533_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_538_; 
lean_dec(v_var_534_);
v___x_536_ = lean_box(v___x_535_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_536_);
v___x_538_ = v___x_530_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
else
{
uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_540_ = l_Lean_instBEqFVarId_beq(v_fvarId_517_, v_var_534_);
lean_dec(v_var_534_);
v___x_541_ = lean_box(v___x_540_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_541_);
v___x_543_ = v___x_530_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
lean_dec(v_val_532_);
v___x_545_ = 0;
v___x_546_ = lean_box(v___x_545_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_546_);
v___x_548_ = v___x_530_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
else
{
uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec(v_a_528_);
v___x_550_ = 0;
v___x_551_ = lean_box(v___x_550_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_551_);
v___x_553_ = v___x_530_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_527_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_527_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_517_ = stack[0].m_obj;
lean_object* v_i_518_ = stack[1].m_obj;
lean_object* v_y_519_ = stack[2].m_obj;
lean_object* v_a_520_ = stack[3].m_obj;
lean_object* v_res_564_;
v_res_564_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_517_, v_i_518_, v_y_519_, v_a_520_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object* v_fvarId_565_, lean_object* v_i_566_, lean_object* v_y_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_565_, v_i_566_, v_y_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec(v_y_567_);
lean_dec(v_i_566_);
lean_dec(v_fvarId_565_);
return v_res_570_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object* v_fvarId_571_, lean_object* v_i_572_, lean_object* v_y_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_571_, v_i_572_, v_y_573_, v_a_575_);
return v___x_579_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_571_ = stack[0].m_obj;
lean_object* v_i_572_ = stack[1].m_obj;
lean_object* v_y_573_ = stack[2].m_obj;
lean_object* v_a_574_ = stack[3].m_obj;
lean_object* v_a_575_ = stack[4].m_obj;
lean_object* v_a_576_ = stack[5].m_obj;
lean_object* v_a_577_ = stack[6].m_obj;
lean_object* v_res_580_;
v_res_580_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(v_fvarId_571_, v_i_572_, v_y_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
stack->m_obj
 = v_res_580_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object* v_fvarId_581_, lean_object* v_i_582_, lean_object* v_y_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(v_fvarId_581_, v_i_582_, v_y_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_y_583_);
lean_dec(v_i_582_);
lean_dec(v_fvarId_581_);
return v_res_589_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object* v_fvarId_590_, lean_object* v_i_591_, lean_object* v_y_592_, lean_object* v_a_593_){
_start:
{
uint8_t v___x_595_; lean_object* v___x_596_; 
v___x_595_ = 1;
v___x_596_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_595_, v_y_592_, v_a_593_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_624_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_624_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_624_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_624_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
if (lean_obj_tag(v_a_597_) == 1)
{
lean_object* v_val_601_; 
v_val_601_ = lean_ctor_get(v_a_597_, 0);
lean_inc(v_val_601_);
lean_dec_ref_known(v_a_597_, 1);
if (lean_obj_tag(v_val_601_) == 7)
{
lean_object* v_i_602_; lean_object* v_var_603_; uint8_t v___x_604_; 
v_i_602_ = lean_ctor_get(v_val_601_, 0);
lean_inc(v_i_602_);
v_var_603_ = lean_ctor_get(v_val_601_, 1);
lean_inc(v_var_603_);
lean_dec_ref_known(v_val_601_, 2);
v___x_604_ = lean_nat_dec_eq(v_i_591_, v_i_602_);
lean_dec(v_i_602_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec(v_var_603_);
v___x_605_ = lean_box(v___x_604_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_605_);
v___x_607_ = v___x_599_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
else
{
uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_609_ = l_Lean_instBEqFVarId_beq(v_fvarId_590_, v_var_603_);
lean_dec(v_var_603_);
v___x_610_ = lean_box(v___x_609_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_610_);
v___x_612_ = v___x_599_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
lean_dec(v_val_601_);
v___x_614_ = 0;
v___x_615_ = lean_box(v___x_614_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_615_);
v___x_617_ = v___x_599_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
else
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
lean_dec(v_a_597_);
v___x_619_ = 0;
v___x_620_ = lean_box(v___x_619_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_620_);
v___x_622_ = v___x_599_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_a_625_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_596_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_596_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_590_ = stack[0].m_obj;
lean_object* v_i_591_ = stack[1].m_obj;
lean_object* v_y_592_ = stack[2].m_obj;
lean_object* v_a_593_ = stack[3].m_obj;
lean_object* v_res_633_;
v_res_633_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_590_, v_i_591_, v_y_592_, v_a_593_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object* v_fvarId_634_, lean_object* v_i_635_, lean_object* v_y_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_634_, v_i_635_, v_y_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec(v_y_636_);
lean_dec(v_i_635_);
lean_dec(v_fvarId_634_);
return v_res_639_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object* v_fvarId_640_, lean_object* v_i_641_, lean_object* v_y_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_640_, v_i_641_, v_y_642_, v_a_644_);
return v___x_648_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_640_ = stack[0].m_obj;
lean_object* v_i_641_ = stack[1].m_obj;
lean_object* v_y_642_ = stack[2].m_obj;
lean_object* v_a_643_ = stack[3].m_obj;
lean_object* v_a_644_ = stack[4].m_obj;
lean_object* v_a_645_ = stack[5].m_obj;
lean_object* v_a_646_ = stack[6].m_obj;
lean_object* v_res_649_;
v_res_649_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(v_fvarId_640_, v_i_641_, v_y_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
stack->m_obj
 = v_res_649_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object* v_fvarId_650_, lean_object* v_i_651_, lean_object* v_y_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(v_fvarId_650_, v_i_651_, v_y_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_y_652_);
lean_dec(v_i_651_);
lean_dec(v_fvarId_650_);
return v_res_658_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object* v_fvarId_659_, lean_object* v_i_660_, lean_object* v_offset_661_, lean_object* v_y_662_, lean_object* v_a_663_){
_start:
{
uint8_t v___x_665_; lean_object* v___x_666_; 
v___x_665_ = 1;
v___x_666_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_665_, v_y_662_, v_a_663_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_700_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_700_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_700_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_700_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
if (lean_obj_tag(v_a_667_) == 1)
{
lean_object* v_val_671_; 
v_val_671_ = lean_ctor_get(v_a_667_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v_a_667_, 1);
if (lean_obj_tag(v_val_671_) == 8)
{
lean_object* v_n_672_; lean_object* v_offset_673_; lean_object* v_var_674_; uint8_t v___x_675_; 
v_n_672_ = lean_ctor_get(v_val_671_, 0);
lean_inc(v_n_672_);
v_offset_673_ = lean_ctor_get(v_val_671_, 1);
lean_inc(v_offset_673_);
v_var_674_ = lean_ctor_get(v_val_671_, 2);
lean_inc(v_var_674_);
lean_dec_ref_known(v_val_671_, 3);
v___x_675_ = lean_nat_dec_eq(v_i_660_, v_n_672_);
lean_dec(v_n_672_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_dec(v_var_674_);
lean_dec(v_offset_673_);
v___x_676_ = lean_box(v___x_675_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_676_);
v___x_678_ = v___x_669_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
else
{
uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_eq(v_offset_661_, v_offset_673_);
lean_dec(v_offset_673_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_683_; 
lean_dec(v_var_674_);
v___x_681_ = lean_box(v___x_680_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_681_);
v___x_683_ = v___x_669_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
else
{
uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_685_ = l_Lean_instBEqFVarId_beq(v_fvarId_659_, v_var_674_);
lean_dec(v_var_674_);
v___x_686_ = lean_box(v___x_685_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_686_);
v___x_688_ = v___x_669_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
lean_dec(v_val_671_);
v___x_690_ = 0;
v___x_691_ = lean_box(v___x_690_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_691_);
v___x_693_ = v___x_669_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
lean_dec(v_a_667_);
v___x_695_ = 0;
v___x_696_ = lean_box(v___x_695_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_696_);
v___x_698_ = v___x_669_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_666_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_666_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_659_ = stack[0].m_obj;
lean_object* v_i_660_ = stack[1].m_obj;
lean_object* v_offset_661_ = stack[2].m_obj;
lean_object* v_y_662_ = stack[3].m_obj;
lean_object* v_a_663_ = stack[4].m_obj;
lean_object* v_res_709_;
v_res_709_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_659_, v_i_660_, v_offset_661_, v_y_662_, v_a_663_);
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object* v_fvarId_710_, lean_object* v_i_711_, lean_object* v_offset_712_, lean_object* v_y_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_710_, v_i_711_, v_offset_712_, v_y_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec(v_y_713_);
lean_dec(v_offset_712_);
lean_dec(v_i_711_);
lean_dec(v_fvarId_710_);
return v_res_716_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object* v_fvarId_717_, lean_object* v_i_718_, lean_object* v_offset_719_, lean_object* v_y_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_717_, v_i_718_, v_offset_719_, v_y_720_, v_a_722_);
return v___x_726_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_717_ = stack[0].m_obj;
lean_object* v_i_718_ = stack[1].m_obj;
lean_object* v_offset_719_ = stack[2].m_obj;
lean_object* v_y_720_ = stack[3].m_obj;
lean_object* v_a_721_ = stack[4].m_obj;
lean_object* v_a_722_ = stack[5].m_obj;
lean_object* v_a_723_ = stack[6].m_obj;
lean_object* v_a_724_ = stack[7].m_obj;
lean_object* v_res_727_;
v_res_727_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(v_fvarId_717_, v_i_718_, v_offset_719_, v_y_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
stack->m_obj
 = v_res_727_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object* v_fvarId_728_, lean_object* v_i_729_, lean_object* v_offset_730_, lean_object* v_y_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(v_fvarId_728_, v_i_729_, v_offset_730_, v_y_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_y_731_);
lean_dec(v_offset_730_);
lean_dec(v_i_729_);
lean_dec(v_fvarId_728_);
return v_res_737_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_toApplicative_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_780_; 
v___x_744_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_745_ = l_StateRefT_x27_instMonad___redArg(v___x_744_);
v_toApplicative_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_745_, 1);
lean_dec(v_unused_781_);
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_780_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_toApplicative_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_780_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_toFunctor_750_; lean_object* v_toSeq_751_; lean_object* v_toSeqLeft_752_; lean_object* v_toSeqRight_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_778_; 
v_toFunctor_750_ = lean_ctor_get(v_toApplicative_746_, 0);
v_toSeq_751_ = lean_ctor_get(v_toApplicative_746_, 2);
v_toSeqLeft_752_ = lean_ctor_get(v_toApplicative_746_, 3);
v_toSeqRight_753_ = lean_ctor_get(v_toApplicative_746_, 4);
v_isSharedCheck_778_ = !lean_is_exclusive(v_toApplicative_746_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_toApplicative_746_, 1);
lean_dec(v_unused_779_);
v___x_755_ = v_toApplicative_746_;
v_isShared_756_ = v_isSharedCheck_778_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_toSeqRight_753_);
lean_inc(v_toSeqLeft_752_);
lean_inc(v_toSeq_751_);
lean_inc(v_toFunctor_750_);
lean_dec(v_toApplicative_746_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_778_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___x_766_; 
v___f_757_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_758_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_750_);
v___f_759_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_759_, 0, v_toFunctor_750_);
v___f_760_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_760_, 0, v_toFunctor_750_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___f_759_);
lean_ctor_set(v___x_761_, 1, v___f_760_);
v___f_762_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_762_, 0, v_toSeqRight_753_);
v___f_763_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_763_, 0, v_toSeqLeft_752_);
v___f_764_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_764_, 0, v_toSeq_751_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 4, v___f_762_);
lean_ctor_set(v___x_755_, 3, v___f_763_);
lean_ctor_set(v___x_755_, 2, v___f_764_);
lean_ctor_set(v___x_755_, 1, v___f_757_);
lean_ctor_set(v___x_755_, 0, v___x_761_);
v___x_766_ = v___x_755_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___f_757_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v___f_764_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v___f_763_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v___f_762_);
v___x_766_ = v_reuseFailAlloc_777_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___f_758_);
lean_ctor_set(v___x_748_, 0, v___x_766_);
v___x_768_ = v___x_748_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___f_758_);
v___x_768_ = v_reuseFailAlloc_776_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___x_883__overap_774_; lean_object* v___x_775_; 
v___x_769_ = l_StateRefT_x27_instMonad___redArg(v___x_768_);
v___x_770_ = 0;
v___x_771_ = lean_box(v___x_770_);
v___x_772_ = l_instInhabitedOfMonad___redArg(v___x_769_, v___x_771_);
v___f_773_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_773_, 0, v___x_772_);
v___x_883__overap_774_ = lean_panic_fn_borrowed(v___f_773_, v_msg_738_);
lean_dec_ref(v___f_773_);
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
v___x_775_ = lean_apply_5(v___x_883__overap_774_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, lean_box(0));
return v___x_775_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_738_ = stack[0].m_obj;
lean_object* v___y_739_ = stack[1].m_obj;
lean_object* v___y_740_ = stack[2].m_obj;
lean_object* v___y_741_ = stack[3].m_obj;
lean_object* v___y_742_ = stack[4].m_obj;
lean_object* v_res_782_;
v_res_782_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v_msg_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v_msg_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_789_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_792_ = lean_unsigned_to_nat(13u);
v___x_793_ = lean_unsigned_to_nat(174u);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0));
v___x_795_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_796_ = l_mkPanicMessageWithDecl(v___x_795_, v___x_794_, v___x_793_, v___x_792_, v___x_791_);
return v___x_796_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object* v_selfId_797_, lean_object* v_as_798_, size_t v_sz_799_, size_t v_i_800_, lean_object* v_b_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_a_808_; uint8_t v___x_812_; 
v___x_812_ = lean_usize_dec_lt(v_i_800_, v_sz_799_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v_b_801_);
return v___x_813_;
}
else
{
lean_object* v_fst_814_; lean_object* v_snd_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_852_; 
v_fst_814_ = lean_ctor_get(v_b_801_, 0);
v_snd_815_ = lean_ctor_get(v_b_801_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_b_801_);
if (v_isSharedCheck_852_ == 0)
{
v___x_817_ = v_b_801_;
v_isShared_818_ = v_isSharedCheck_852_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_snd_815_);
lean_inc(v_fst_814_);
lean_dec(v_b_801_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_852_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_a_819_; lean_object* v___y_821_; 
v_a_819_ = lean_array_uget_borrowed(v_as_798_, v_i_800_);
switch(lean_obj_tag(v_a_819_))
{
case 3:
{
lean_object* v_i_840_; lean_object* v_y_841_; lean_object* v___x_842_; 
v_i_840_ = lean_ctor_get(v_a_819_, 1);
v_y_841_ = lean_ctor_get(v_a_819_, 2);
v___x_842_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_selfId_797_, v_i_840_, v_y_841_, v___y_803_);
v___y_821_ = v___x_842_;
goto v___jp_820_;
}
case 4:
{
lean_object* v_i_843_; lean_object* v_y_844_; lean_object* v___x_845_; 
v_i_843_ = lean_ctor_get(v_a_819_, 1);
v_y_844_ = lean_ctor_get(v_a_819_, 2);
v___x_845_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_selfId_797_, v_i_843_, v_y_844_, v___y_803_);
v___y_821_ = v___x_845_;
goto v___jp_820_;
}
case 5:
{
lean_object* v_i_846_; lean_object* v_offset_847_; lean_object* v_y_848_; lean_object* v___x_849_; 
v_i_846_ = lean_ctor_get(v_a_819_, 1);
v_offset_847_ = lean_ctor_get(v_a_819_, 2);
v_y_848_ = lean_ctor_get(v_a_819_, 3);
v___x_849_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_selfId_797_, v_i_846_, v_offset_847_, v_y_848_, v___y_803_);
v___y_821_ = v___x_849_;
goto v___jp_820_;
}
default: 
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1);
v___x_851_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v___x_850_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
v___y_821_ = v___x_851_;
goto v___jp_820_;
}
}
v___jp_820_:
{
if (lean_obj_tag(v___y_821_) == 0)
{
lean_object* v_a_822_; uint8_t v___x_823_; 
v_a_822_ = lean_ctor_get(v___y_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___y_821_, 1);
v___x_823_ = lean_unbox(v_a_822_);
lean_dec(v_a_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_826_; 
lean_inc(v_a_819_);
v___x_824_ = lean_array_push(v_fst_814_, v_a_819_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_824_);
v___x_826_ = v___x_817_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_snd_815_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
v_a_808_ = v___x_826_;
goto v___jp_807_;
}
}
else
{
lean_object* v___x_828_; lean_object* v___x_830_; 
lean_inc(v_a_819_);
v___x_828_ = lean_array_push(v_snd_815_, v_a_819_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_828_);
v___x_830_ = v___x_817_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_fst_814_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v_a_808_ = v___x_830_;
goto v___jp_807_;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_del_object(v___x_817_);
lean_dec(v_snd_815_);
lean_dec(v_fst_814_);
v_a_832_ = lean_ctor_get(v___y_821_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___y_821_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___y_821_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___y_821_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
}
v___jp_807_:
{
size_t v___x_809_; size_t v___x_810_; 
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_add(v_i_800_, v___x_809_);
v_i_800_ = v___x_810_;
v_b_801_ = v_a_808_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_selfId_797_ = stack[0].m_obj;
lean_object* v_as_798_ = stack[1].m_obj;
size_t v_sz_799_ = stack[2].m_num;
size_t v_i_800_ = stack[3].m_num;
lean_object* v_b_801_ = stack[4].m_obj;
lean_object* v___y_802_ = stack[5].m_obj;
lean_object* v___y_803_ = stack[6].m_obj;
lean_object* v___y_804_ = stack[7].m_obj;
lean_object* v___y_805_ = stack[8].m_obj;
lean_object* v_res_853_;
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_797_, v_as_798_, v_sz_799_, v_i_800_, v_b_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
stack->m_obj
 = v_res_853_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object* v_selfId_854_, lean_object* v_as_855_, lean_object* v_sz_856_, lean_object* v_i_857_, lean_object* v_b_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
size_t v_sz_boxed_864_; size_t v_i_boxed_865_; lean_object* v_res_866_; 
v_sz_boxed_864_ = lean_unbox_usize(v_sz_856_);
lean_dec(v_sz_856_);
v_i_boxed_865_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_854_, v_as_855_, v_sz_boxed_864_, v_i_boxed_865_, v_b_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec_ref(v_as_855_);
lean_dec(v_selfId_854_);
return v_res_866_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object* v_selfId_869_, lean_object* v_sets_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; size_t v_sz_877_; size_t v___x_878_; lean_object* v___x_879_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0));
v_sz_877_ = lean_array_size(v_sets_870_);
v___x_878_ = ((size_t)0ULL);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_869_, v_sets_870_, v_sz_877_, v___x_878_, v___x_876_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_896_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_896_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_896_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_896_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_fst_884_; lean_object* v_snd_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_895_; 
v_fst_884_ = lean_ctor_get(v_a_880_, 0);
v_snd_885_ = lean_ctor_get(v_a_880_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_880_);
if (v_isSharedCheck_895_ == 0)
{
v___x_887_ = v_a_880_;
v_isShared_888_ = v_isSharedCheck_895_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_snd_885_);
lean_inc(v_fst_884_);
lean_dec(v_a_880_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_895_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_fst_884_);
lean_ctor_set(v___x_887_, 0, v_snd_885_);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_snd_885_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_fst_884_);
v___x_890_ = v_reuseFailAlloc_894_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_892_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_890_);
v___x_892_ = v___x_882_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
else
{
return v___x_879_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_0interp(lean_interpreter_value* stack)
{
lean_object* v_selfId_869_ = stack[0].m_obj;
lean_object* v_sets_870_ = stack[1].m_obj;
lean_object* v_a_871_ = stack[2].m_obj;
lean_object* v_a_872_ = stack[3].m_obj;
lean_object* v_a_873_ = stack[4].m_obj;
lean_object* v_a_874_ = stack[5].m_obj;
lean_object* v_res_897_;
v_res_897_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_selfId_869_, v_sets_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
stack->m_obj
 = v_res_897_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object* v_selfId_898_, lean_object* v_sets_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_selfId_898_, v_sets_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec_ref(v_sets_899_);
lean_dec(v_selfId_898_);
return v_res_905_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object* v_target_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_snd_909_; 
v_snd_909_ = lean_ctor_get(v_a_907_, 1);
lean_inc(v_snd_909_);
switch(lean_obj_tag(v_snd_909_))
{
case 7:
{
lean_object* v_fst_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_928_; 
v_fst_910_ = lean_ctor_get(v_a_907_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_a_907_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_a_907_, 1);
lean_dec(v_unused_929_);
v___x_912_ = v_a_907_;
v_isShared_913_ = v_isSharedCheck_928_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_fst_910_);
lean_dec(v_a_907_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_928_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_fvarId_914_; lean_object* v_k_915_; uint8_t v___x_916_; 
v_fvarId_914_ = lean_ctor_get(v_snd_909_, 0);
v_k_915_ = lean_ctor_get(v_snd_909_, 3);
v___x_916_ = l_Lean_instBEqFVarId_beq(v_target_906_, v_fvarId_914_);
if (v___x_916_ == 0)
{
lean_object* v___x_918_; 
if (v_isShared_913_ == 0)
{
v___x_918_ = v___x_912_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_fst_910_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_snd_909_);
v___x_918_ = v_reuseFailAlloc_920_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
else
{
uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
lean_inc_ref(v_k_915_);
v___x_921_ = 1;
v___x_922_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_921_, v_snd_909_);
lean_dec_ref_known(v_snd_909_, 4);
v___x_923_ = lean_array_push(v_fst_910_, v___x_922_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_k_915_);
lean_ctor_set(v___x_912_, 0, v___x_923_);
v___x_925_ = v___x_912_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_915_);
v___x_925_ = v_reuseFailAlloc_927_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
v_a_907_ = v___x_925_;
goto _start;
}
}
}
}
case 9:
{
lean_object* v_fst_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_948_; 
v_fst_930_ = lean_ctor_get(v_a_907_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_a_907_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_a_907_, 1);
lean_dec(v_unused_949_);
v___x_932_ = v_a_907_;
v_isShared_933_ = v_isSharedCheck_948_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_fst_930_);
lean_dec(v_a_907_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_948_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_fvarId_934_; lean_object* v_k_935_; uint8_t v___x_936_; 
v_fvarId_934_ = lean_ctor_get(v_snd_909_, 0);
v_k_935_ = lean_ctor_get(v_snd_909_, 5);
v___x_936_ = l_Lean_instBEqFVarId_beq(v_target_906_, v_fvarId_934_);
if (v___x_936_ == 0)
{
lean_object* v___x_938_; 
if (v_isShared_933_ == 0)
{
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_fst_930_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_snd_909_);
v___x_938_ = v_reuseFailAlloc_940_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; 
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
else
{
uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
lean_inc_ref(v_k_935_);
v___x_941_ = 1;
v___x_942_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_941_, v_snd_909_);
lean_dec_ref_known(v_snd_909_, 6);
v___x_943_ = lean_array_push(v_fst_930_, v___x_942_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v_k_935_);
lean_ctor_set(v___x_932_, 0, v___x_943_);
v___x_945_ = v___x_932_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_k_935_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
v_a_907_ = v___x_945_;
goto _start;
}
}
}
}
case 8:
{
lean_object* v_fst_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_968_; 
v_fst_950_ = lean_ctor_get(v_a_907_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v_a_907_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v_a_907_, 1);
lean_dec(v_unused_969_);
v___x_952_ = v_a_907_;
v_isShared_953_ = v_isSharedCheck_968_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_fst_950_);
lean_dec(v_a_907_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_968_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_fvarId_954_; lean_object* v_k_955_; uint8_t v___x_956_; 
v_fvarId_954_ = lean_ctor_get(v_snd_909_, 0);
v_k_955_ = lean_ctor_get(v_snd_909_, 3);
v___x_956_ = l_Lean_instBEqFVarId_beq(v_target_906_, v_fvarId_954_);
if (v___x_956_ == 0)
{
lean_object* v___x_958_; 
if (v_isShared_953_ == 0)
{
v___x_958_ = v___x_952_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_fst_950_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_snd_909_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; 
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
else
{
uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
lean_inc_ref(v_k_955_);
v___x_961_ = 1;
v___x_962_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_961_, v_snd_909_);
lean_dec_ref_known(v_snd_909_, 4);
v___x_963_ = lean_array_push(v_fst_950_, v___x_962_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_k_955_);
lean_ctor_set(v___x_952_, 0, v___x_963_);
v___x_965_ = v___x_952_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_955_);
v___x_965_ = v_reuseFailAlloc_967_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
v_a_907_ = v___x_965_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_fst_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_fst_970_ = lean_ctor_get(v_a_907_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v_a_907_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v_a_907_, 1);
lean_dec(v_unused_979_);
v___x_972_ = v_a_907_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_fst_970_);
lean_dec(v_a_907_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_fst_970_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_snd_909_);
v___x_975_ = v_reuseFailAlloc_977_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_906_ = stack[0].m_obj;
lean_object* v_a_907_ = stack[1].m_obj;
lean_object* v_res_980_;
v_res_980_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_906_, v_a_907_);
stack->m_obj
 = v_res_980_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object* v_target_981_, lean_object* v_a_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_981_, v_a_982_);
lean_dec(v_target_981_);
return v_res_984_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object* v_target_985_, lean_object* v_k_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_sets_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_sets_992_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v_sets_992_);
lean_ctor_set(v___x_993_, 1, v_k_986_);
v___x_994_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_985_, v___x_993_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1011_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1011_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1011_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_fst_999_; lean_object* v_snd_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1010_; 
v_fst_999_ = lean_ctor_get(v_a_995_, 0);
v_snd_1000_ = lean_ctor_get(v_a_995_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_a_995_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1002_ = v_a_995_;
v_isShared_1003_ = v_isSharedCheck_1010_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_snd_1000_);
lean_inc(v_fst_999_);
lean_dec(v_a_995_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1010_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_fst_999_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_snd_1000_);
v___x_1005_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1005_);
v___x_1007_ = v___x_997_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
else
{
return v___x_994_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_985_ = stack[0].m_obj;
lean_object* v_k_986_ = stack[1].m_obj;
lean_object* v_a_987_ = stack[2].m_obj;
lean_object* v_a_988_ = stack[3].m_obj;
lean_object* v_a_989_ = stack[4].m_obj;
lean_object* v_a_990_ = stack[5].m_obj;
lean_object* v_res_1012_;
v_res_1012_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_target_985_, v_k_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
stack->m_obj
 = v_res_1012_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object* v_target_1013_, lean_object* v_k_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_target_1013_, v_k_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_target_1013_);
return v_res_1020_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object* v_target_1021_, lean_object* v_inst_1022_, lean_object* v_a_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_1021_, v_a_1023_);
return v___x_1029_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_1021_ = stack[0].m_obj;
lean_object* v_a_1023_ = stack[2].m_obj;
lean_object* v___y_1024_ = stack[3].m_obj;
lean_object* v___y_1025_ = stack[4].m_obj;
lean_object* v___y_1026_ = stack[5].m_obj;
lean_object* v___y_1027_ = stack[6].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(v_target_1021_, lean_box(0), v_a_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object* v_target_1031_, lean_object* v_inst_1032_, lean_object* v_a_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(v_target_1031_, v_inst_1032_, v_a_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v_target_1031_);
return v_res_1039_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3));
v___x_1048_ = l_Lean_Expr_const___override(v___x_1047_, v___x_1046_);
return v___x_1048_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1049_, lean_object* v_mask_1050_, lean_object* v_origAllocId_1051_, lean_object* v_a_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_a_1060_; uint8_t v___x_1064_; 
v___x_1064_ = lean_nat_dec_lt(v_a_1052_, v_upperBound_1049_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
lean_dec(v_a_1052_);
lean_dec(v_origAllocId_1051_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_b_1053_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_array_fget_borrowed(v_mask_1050_, v_a_1052_);
if (lean_obj_tag(v___x_1066_) == 0)
{
uint8_t v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1067_ = 1;
v___x_1068_ = 0;
v___x_1069_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1));
v___x_1070_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1069_, v___y_1055_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_origAllocId_1051_);
lean_inc(v_a_1052_);
v___x_1073_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_a_1052_);
lean_ctor_set(v___x_1073_, 1, v_origAllocId_1051_);
v___x_1074_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1067_, v_a_1071_, v___x_1072_, v___x_1073_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v_fvarId_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v_fvarId_1076_ = lean_ctor_get(v_a_1075_, 0);
v___x_1077_ = lean_unsigned_to_nat(1u);
v___x_1078_ = lean_box(0);
lean_inc(v_fvarId_1076_);
v___x_1079_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1079_, 0, v_fvarId_1076_);
lean_ctor_set(v___x_1079_, 1, v___x_1077_);
lean_ctor_set(v___x_1079_, 2, v___x_1078_);
lean_ctor_set(v___x_1079_, 3, v_b_1053_);
lean_ctor_set_uint8(v___x_1079_, sizeof(void*)*4, v___x_1064_);
lean_ctor_set_uint8(v___x_1079_, sizeof(void*)*4 + 1, v___x_1068_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_a_1075_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v_a_1060_ = v___x_1080_;
goto v___jp_1059_;
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v_b_1053_);
lean_dec(v_a_1052_);
lean_dec(v_origAllocId_1051_);
v_a_1081_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1074_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1074_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v_b_1053_);
lean_dec(v_a_1052_);
lean_dec(v_origAllocId_1051_);
v_a_1089_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1070_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1070_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
v_a_1060_ = v_b_1053_;
goto v___jp_1059_;
}
}
v___jp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_add(v_a_1052_, v___x_1061_);
lean_dec(v_a_1052_);
v_a_1052_ = v___x_1062_;
v_b_1053_ = v_a_1060_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1049_ = stack[0].m_obj;
lean_object* v_mask_1050_ = stack[1].m_obj;
lean_object* v_origAllocId_1051_ = stack[2].m_obj;
lean_object* v_a_1052_ = stack[3].m_obj;
lean_object* v_b_1053_ = stack[4].m_obj;
lean_object* v___y_1054_ = stack[5].m_obj;
lean_object* v___y_1055_ = stack[6].m_obj;
lean_object* v___y_1056_ = stack[7].m_obj;
lean_object* v___y_1057_ = stack[8].m_obj;
lean_object* v_res_1097_;
v_res_1097_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1049_, v_mask_1050_, v_origAllocId_1051_, v_a_1052_, v_b_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
stack->m_obj
 = v_res_1097_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1098_, lean_object* v_mask_1099_, lean_object* v_origAllocId_1100_, lean_object* v_a_1101_, lean_object* v_b_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1098_, v_mask_1099_, v_origAllocId_1100_, v_a_1101_, v_b_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec_ref(v_mask_1099_);
lean_dec(v_upperBound_1098_);
return v_res_1108_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object* v_origAllocId_1109_, lean_object* v_mask_1110_, lean_object* v_resetJpId_1111_, lean_object* v_isSharedId_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_code_1126_; lean_object* v___x_1127_; 
lean_inc(v_origAllocId_1109_);
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_origAllocId_1109_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_isSharedId_1112_);
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_array_get_size(v_mask_1110_);
v___x_1122_ = lean_unsigned_to_nat(2u);
v___x_1123_ = lean_mk_empty_array_with_capacity(v___x_1122_);
v___x_1124_ = lean_array_push(v___x_1123_, v___x_1118_);
v___x_1125_ = lean_array_push(v___x_1124_, v___x_1119_);
v_code_1126_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1126_, 0, v_resetJpId_1111_);
lean_ctor_set(v_code_1126_, 1, v___x_1125_);
v___x_1127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v___x_1121_, v_mask_1110_, v_origAllocId_1109_, v___x_1120_, v_code_1126_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
return v___x_1127_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_origAllocId_1109_ = stack[0].m_obj;
lean_object* v_mask_1110_ = stack[1].m_obj;
lean_object* v_resetJpId_1111_ = stack[2].m_obj;
lean_object* v_isSharedId_1112_ = stack[3].m_obj;
lean_object* v_a_1113_ = stack[4].m_obj;
lean_object* v_a_1114_ = stack[5].m_obj;
lean_object* v_a_1115_ = stack[6].m_obj;
lean_object* v_a_1116_ = stack[7].m_obj;
lean_object* v_res_1128_;
v_res_1128_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_1109_, v_mask_1110_, v_resetJpId_1111_, v_isSharedId_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
stack->m_obj
 = v_res_1128_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object* v_origAllocId_1129_, lean_object* v_mask_1130_, lean_object* v_resetJpId_1131_, lean_object* v_isSharedId_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_1129_, v_mask_1130_, v_resetJpId_1131_, v_isSharedId_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_mask_1130_);
return v_res_1138_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object* v_upperBound_1139_, lean_object* v_mask_1140_, lean_object* v_origAllocId_1141_, lean_object* v_inst_1142_, lean_object* v_R_1143_, lean_object* v_a_1144_, lean_object* v_b_1145_, lean_object* v_c_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1139_, v_mask_1140_, v_origAllocId_1141_, v_a_1144_, v_b_1145_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1139_ = stack[0].m_obj;
lean_object* v_mask_1140_ = stack[1].m_obj;
lean_object* v_origAllocId_1141_ = stack[2].m_obj;
lean_object* v_a_1144_ = stack[5].m_obj;
lean_object* v_b_1145_ = stack[6].m_obj;
lean_object* v___y_1147_ = stack[8].m_obj;
lean_object* v___y_1148_ = stack[9].m_obj;
lean_object* v___y_1149_ = stack[10].m_obj;
lean_object* v___y_1150_ = stack[11].m_obj;
lean_object* v_res_1153_;
v_res_1153_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(v_upperBound_1139_, v_mask_1140_, v_origAllocId_1141_, lean_box(0), lean_box(0), v_a_1144_, v_b_1145_, lean_box(0), v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
stack->m_obj
 = v_res_1153_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1154_, lean_object* v_mask_1155_, lean_object* v_origAllocId_1156_, lean_object* v_inst_1157_, lean_object* v_R_1158_, lean_object* v_a_1159_, lean_object* v_b_1160_, lean_object* v_c_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(v_upperBound_1154_, v_mask_1155_, v_origAllocId_1156_, v_inst_1157_, v_R_1158_, v_a_1159_, v_b_1160_, v_c_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec_ref(v_mask_1155_);
lean_dec(v_upperBound_1154_);
return v_res_1167_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object* v_as_1168_, size_t v_sz_1169_, size_t v_i_1170_, lean_object* v_b_1171_){
_start:
{
lean_object* v_a_1174_; uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_lt(v_i_1170_, v_sz_1169_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_b_1171_);
return v___x_1179_;
}
else
{
lean_object* v_a_1180_; 
v_a_1180_ = lean_array_uget_borrowed(v_as_1168_, v_i_1170_);
if (lean_obj_tag(v_a_1180_) == 1)
{
lean_object* v_val_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; 
v_val_1181_ = lean_ctor_get(v_a_1180_, 0);
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = 0;
lean_inc(v_val_1181_);
v___x_1184_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1184_, 0, v_val_1181_);
lean_ctor_set(v___x_1184_, 1, v___x_1182_);
lean_ctor_set(v___x_1184_, 2, v_b_1171_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*3, v___x_1178_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*3 + 1, v___x_1183_);
v_a_1174_ = v___x_1184_;
goto v___jp_1173_;
}
else
{
v_a_1174_ = v_b_1171_;
goto v___jp_1173_;
}
}
v___jp_1173_:
{
size_t v___x_1175_; size_t v___x_1176_; 
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_add(v_i_1170_, v___x_1175_);
v_i_1170_ = v___x_1176_;
v_b_1171_ = v_a_1174_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1168_ = stack[0].m_obj;
size_t v_sz_1169_ = stack[1].m_num;
size_t v_i_1170_ = stack[2].m_num;
lean_object* v_b_1171_ = stack[3].m_obj;
lean_object* v_res_1185_;
v_res_1185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1168_, v_sz_1169_, v_i_1170_, v_b_1171_);
stack->m_obj
 = v_res_1185_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object* v_as_1186_, lean_object* v_sz_1187_, lean_object* v_i_1188_, lean_object* v_b_1189_, lean_object* v___y_1190_){
_start:
{
size_t v_sz_boxed_1191_; size_t v_i_boxed_1192_; lean_object* v_res_1193_; 
v_sz_boxed_1191_ = lean_unbox_usize(v_sz_1187_);
lean_dec(v_sz_1187_);
v_i_boxed_1192_ = lean_unbox_usize(v_i_1188_);
lean_dec(v_i_1188_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1186_, v_sz_boxed_1191_, v_i_boxed_1192_, v_b_1189_);
lean_dec_ref(v_as_1186_);
return v_res_1193_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_unsigned_to_nat(2u);
v___x_1196_ = lean_mk_empty_array_with_capacity(v___x_1195_);
v___x_1197_ = lean_array_push(v___x_1196_, v___x_1194_);
return v___x_1197_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object* v_origAllocId_1198_, lean_object* v_mask_1199_, lean_object* v_resetJpId_1200_, lean_object* v_isSharedId_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_code_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v_code_1215_; size_t v_sz_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_isSharedId_1201_);
v___x_1208_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0);
v___x_1209_ = lean_array_push(v___x_1208_, v___x_1207_);
v_code_1210_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1210_, 0, v_resetJpId_1200_);
lean_ctor_set(v_code_1210_, 1, v___x_1209_);
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = 1;
v___x_1213_ = 0;
v___x_1214_ = lean_box(0);
v_code_1215_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_code_1215_, 0, v_origAllocId_1198_);
lean_ctor_set(v_code_1215_, 1, v___x_1211_);
lean_ctor_set(v_code_1215_, 2, v___x_1214_);
lean_ctor_set(v_code_1215_, 3, v_code_1210_);
lean_ctor_set_uint8(v_code_1215_, sizeof(void*)*4, v___x_1212_);
lean_ctor_set_uint8(v_code_1215_, sizeof(void*)*4 + 1, v___x_1213_);
v_sz_1216_ = lean_array_size(v_mask_1199_);
v___x_1217_ = ((size_t)0ULL);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_mask_1199_, v_sz_1216_, v___x_1217_, v_code_1215_);
return v___x_1218_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_origAllocId_1198_ = stack[0].m_obj;
lean_object* v_mask_1199_ = stack[1].m_obj;
lean_object* v_resetJpId_1200_ = stack[2].m_obj;
lean_object* v_isSharedId_1201_ = stack[3].m_obj;
lean_object* v_a_1202_ = stack[4].m_obj;
lean_object* v_a_1203_ = stack[5].m_obj;
lean_object* v_a_1204_ = stack[6].m_obj;
lean_object* v_a_1205_ = stack[7].m_obj;
lean_object* v_res_1219_;
v_res_1219_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_1198_, v_mask_1199_, v_resetJpId_1200_, v_isSharedId_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
stack->m_obj
 = v_res_1219_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(lean_object* v_origAllocId_1220_, lean_object* v_mask_1221_, lean_object* v_resetJpId_1222_, lean_object* v_isSharedId_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_1220_, v_mask_1221_, v_resetJpId_1222_, v_isSharedId_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec_ref(v_mask_1221_);
return v_res_1229_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(lean_object* v_as_1230_, size_t v_sz_1231_, size_t v_i_1232_, lean_object* v_b_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1230_, v_sz_1231_, v_i_1232_, v_b_1233_);
return v___x_1239_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1230_ = stack[0].m_obj;
size_t v_sz_1231_ = stack[1].m_num;
size_t v_i_1232_ = stack[2].m_num;
lean_object* v_b_1233_ = stack[3].m_obj;
lean_object* v___y_1234_ = stack[4].m_obj;
lean_object* v___y_1235_ = stack[5].m_obj;
lean_object* v___y_1236_ = stack[6].m_obj;
lean_object* v___y_1237_ = stack[7].m_obj;
lean_object* v_res_1240_;
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(v_as_1230_, v_sz_1231_, v_i_1232_, v_b_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
stack->m_obj
 = v_res_1240_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(lean_object* v_as_1241_, lean_object* v_sz_1242_, lean_object* v_i_1243_, lean_object* v_b_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
size_t v_sz_boxed_1250_; size_t v_i_boxed_1251_; lean_object* v_res_1252_; 
v_sz_boxed_1250_ = lean_unbox_usize(v_sz_1242_);
lean_dec(v_sz_1242_);
v_i_boxed_1251_ = lean_unbox_usize(v_i_1243_);
lean_dec(v_i_1243_);
v_res_1252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(v_as_1241_, v_sz_boxed_1250_, v_i_boxed_1251_, v_b_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v_as_1241_);
return v_res_1252_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1253_, lean_object* v_args_1254_, lean_object* v_origAllocId_1255_, lean_object* v_resetTokenId_1256_, lean_object* v_a_1257_, lean_object* v_b_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_a_1262_; uint8_t v___x_1266_; 
v___x_1266_ = lean_nat_dec_lt(v_a_1257_, v_upperBound_1253_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec(v_a_1257_);
lean_dec(v_resetTokenId_1256_);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1258_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_array_fget_borrowed(v_args_1254_, v_a_1257_);
v___x_1269_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_origAllocId_1255_, v_a_1257_, v___x_1268_, v___y_1259_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; uint8_t v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = lean_unbox(v_a_1270_);
lean_dec(v_a_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; 
lean_inc(v___x_1268_);
lean_inc(v_a_1257_);
lean_inc(v_resetTokenId_1256_);
v___x_1272_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1272_, 0, v_resetTokenId_1256_);
lean_ctor_set(v___x_1272_, 1, v_a_1257_);
lean_ctor_set(v___x_1272_, 2, v___x_1268_);
lean_ctor_set(v___x_1272_, 3, v_b_1258_);
v_a_1262_ = v___x_1272_;
goto v___jp_1261_;
}
else
{
v_a_1262_ = v_b_1258_;
goto v___jp_1261_;
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_b_1258_);
lean_dec(v_a_1257_);
lean_dec(v_resetTokenId_1256_);
v_a_1273_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1269_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1269_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
v___jp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_nat_add(v_a_1257_, v___x_1263_);
lean_dec(v_a_1257_);
v_a_1257_ = v___x_1264_;
v_b_1258_ = v_a_1262_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1253_ = stack[0].m_obj;
lean_object* v_args_1254_ = stack[1].m_obj;
lean_object* v_origAllocId_1255_ = stack[2].m_obj;
lean_object* v_resetTokenId_1256_ = stack[3].m_obj;
lean_object* v_a_1257_ = stack[4].m_obj;
lean_object* v_b_1258_ = stack[5].m_obj;
lean_object* v___y_1259_ = stack[6].m_obj;
lean_object* v_res_1281_;
v_res_1281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1253_, v_args_1254_, v_origAllocId_1255_, v_resetTokenId_1256_, v_a_1257_, v_b_1258_, v___y_1259_);
stack->m_obj
 = v_res_1281_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1282_, lean_object* v_args_1283_, lean_object* v_origAllocId_1284_, lean_object* v_resetTokenId_1285_, lean_object* v_a_1286_, lean_object* v_b_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1282_, v_args_1283_, v_origAllocId_1284_, v_resetTokenId_1285_, v_a_1286_, v_b_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec(v_origAllocId_1284_);
lean_dec_ref(v_args_1283_);
lean_dec(v_upperBound_1282_);
return v_res_1290_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(lean_object* v_resetTokenId_1291_, lean_object* v_info_1292_, uint8_t v_update_1293_, lean_object* v_args_1294_, lean_object* v_contJpId_1295_, lean_object* v_origAllocId_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_code_1308_; lean_object* v___x_1309_; 
lean_inc_n(v_resetTokenId_1291_, 2);
v___x_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_resetTokenId_1291_);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_array_get_size(v_args_1294_);
v___x_1305_ = lean_unsigned_to_nat(1u);
v___x_1306_ = lean_mk_empty_array_with_capacity(v___x_1305_);
v___x_1307_ = lean_array_push(v___x_1306_, v___x_1302_);
v_code_1308_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1308_, 0, v_contJpId_1295_);
lean_ctor_set(v_code_1308_, 1, v___x_1307_);
v___x_1309_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v___x_1304_, v_args_1294_, v_origAllocId_1296_, v_resetTokenId_1291_, v___x_1303_, v_code_1308_, v_a_1298_);
if (lean_obj_tag(v___x_1309_) == 0)
{
if (v_update_1293_ == 0)
{
lean_dec(v_resetTokenId_1291_);
return v___x_1309_;
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1319_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_cidx_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v_cidx_1314_ = lean_ctor_get(v_info_1292_, 1);
lean_inc(v_cidx_1314_);
v___x_1315_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1315_, 0, v_resetTokenId_1291_);
lean_ctor_set(v___x_1315_, 1, v_cidx_1314_);
lean_ctor_set(v___x_1315_, 2, v_a_1310_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1315_);
v___x_1317_ = v___x_1312_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_dec(v_resetTokenId_1291_);
return v___x_1309_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_resetTokenId_1291_ = stack[0].m_obj;
lean_object* v_info_1292_ = stack[1].m_obj;
uint8_t v_update_1293_ = stack[2].m_num;
lean_object* v_args_1294_ = stack[3].m_obj;
lean_object* v_contJpId_1295_ = stack[4].m_obj;
lean_object* v_origAllocId_1296_ = stack[5].m_obj;
lean_object* v_a_1297_ = stack[6].m_obj;
lean_object* v_a_1298_ = stack[7].m_obj;
lean_object* v_a_1299_ = stack[8].m_obj;
lean_object* v_a_1300_ = stack[9].m_obj;
lean_object* v_res_1320_;
v_res_1320_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1291_, v_info_1292_, v_update_1293_, v_args_1294_, v_contJpId_1295_, v_origAllocId_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
stack->m_obj
 = v_res_1320_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(lean_object* v_resetTokenId_1321_, lean_object* v_info_1322_, lean_object* v_update_1323_, lean_object* v_args_1324_, lean_object* v_contJpId_1325_, lean_object* v_origAllocId_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
uint8_t v_update_boxed_1332_; lean_object* v_res_1333_; 
v_update_boxed_1332_ = lean_unbox(v_update_1323_);
v_res_1333_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1321_, v_info_1322_, v_update_boxed_1332_, v_args_1324_, v_contJpId_1325_, v_origAllocId_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_origAllocId_1326_);
lean_dec_ref(v_args_1324_);
lean_dec_ref(v_info_1322_);
return v_res_1333_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(lean_object* v_upperBound_1334_, lean_object* v_args_1335_, lean_object* v_origAllocId_1336_, lean_object* v_resetTokenId_1337_, lean_object* v_inst_1338_, lean_object* v_R_1339_, lean_object* v_a_1340_, lean_object* v_b_1341_, lean_object* v_c_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1334_, v_args_1335_, v_origAllocId_1336_, v_resetTokenId_1337_, v_a_1340_, v_b_1341_, v___y_1344_);
return v___x_1348_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1334_ = stack[0].m_obj;
lean_object* v_args_1335_ = stack[1].m_obj;
lean_object* v_origAllocId_1336_ = stack[2].m_obj;
lean_object* v_resetTokenId_1337_ = stack[3].m_obj;
lean_object* v_a_1340_ = stack[6].m_obj;
lean_object* v_b_1341_ = stack[7].m_obj;
lean_object* v___y_1343_ = stack[9].m_obj;
lean_object* v___y_1344_ = stack[10].m_obj;
lean_object* v___y_1345_ = stack[11].m_obj;
lean_object* v___y_1346_ = stack[12].m_obj;
lean_object* v_res_1349_;
v_res_1349_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(v_upperBound_1334_, v_args_1335_, v_origAllocId_1336_, v_resetTokenId_1337_, lean_box(0), lean_box(0), v_a_1340_, v_b_1341_, lean_box(0), v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
stack->m_obj
 = v_res_1349_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1350_, lean_object* v_args_1351_, lean_object* v_origAllocId_1352_, lean_object* v_resetTokenId_1353_, lean_object* v_inst_1354_, lean_object* v_R_1355_, lean_object* v_a_1356_, lean_object* v_b_1357_, lean_object* v_c_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(v_upperBound_1350_, v_args_1351_, v_origAllocId_1352_, v_resetTokenId_1353_, v_inst_1354_, v_R_1355_, v_a_1356_, v_b_1357_, v_c_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v_origAllocId_1352_);
lean_dec_ref(v_args_1351_);
lean_dec(v_upperBound_1350_);
return v_res_1364_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(lean_object* v_decl_1368_, lean_object* v_info_1369_, lean_object* v_args_1370_, lean_object* v_contJpId_1371_, lean_object* v_selfSets_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1));
v___x_1379_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1378_, v_a_1374_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v_type_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v_type_1381_ = lean_ctor_get(v_decl_1368_, 2);
lean_inc_ref(v_type_1381_);
lean_dec_ref(v_decl_1368_);
v___x_1382_ = 1;
v___x_1383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_info_1369_);
lean_ctor_set(v___x_1383_, 1, v_args_1370_);
v___x_1384_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1382_, v_a_1380_, v_type_1381_, v___x_1383_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v_fvarId_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1402_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v_fvarId_1386_ = lean_ctor_get(v_a_1385_, 0);
lean_inc_n(v_fvarId_1386_, 2);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_fvarId_1386_);
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = lean_mk_empty_array_with_capacity(v___x_1388_);
v___x_1390_ = lean_array_push(v___x_1389_, v___x_1387_);
v___x_1391_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_contJpId_1371_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_fvarId_1386_, v_selfSets_1372_);
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1397_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_a_1393_, v___x_1391_);
lean_dec(v_a_1393_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_a_1385_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1398_);
v___x_1400_ = v___x_1395_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec_ref(v_selfSets_1372_);
lean_dec(v_contJpId_1371_);
v_a_1403_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1384_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1384_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec_ref(v_selfSets_1372_);
lean_dec(v_contJpId_1371_);
lean_dec_ref(v_args_1370_);
lean_dec_ref(v_info_1369_);
lean_dec_ref(v_decl_1368_);
v_a_1411_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1379_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1379_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1368_ = stack[0].m_obj;
lean_object* v_info_1369_ = stack[1].m_obj;
lean_object* v_args_1370_ = stack[2].m_obj;
lean_object* v_contJpId_1371_ = stack[3].m_obj;
lean_object* v_selfSets_1372_ = stack[4].m_obj;
lean_object* v_a_1373_ = stack[5].m_obj;
lean_object* v_a_1374_ = stack[6].m_obj;
lean_object* v_a_1375_ = stack[7].m_obj;
lean_object* v_a_1376_ = stack[8].m_obj;
lean_object* v_res_1419_;
v_res_1419_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1368_, v_info_1369_, v_args_1370_, v_contJpId_1371_, v_selfSets_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
stack->m_obj
 = v_res_1419_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(lean_object* v_decl_1420_, lean_object* v_info_1421_, lean_object* v_args_1422_, lean_object* v_contJpId_1423_, lean_object* v_selfSets_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1420_, v_info_1421_, v_args_1422_, v_contJpId_1423_, v_selfSets_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
return v_res_1430_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(lean_object* v_alt_1431_, lean_object* v_f_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___y_1439_; 
switch(lean_obj_tag(v_alt_1431_))
{
case 0:
{
lean_object* v_code_1458_; 
v_code_1458_ = lean_ctor_get(v_alt_1431_, 2);
lean_inc_ref(v_code_1458_);
v___y_1439_ = v_code_1458_;
goto v___jp_1438_;
}
case 1:
{
lean_object* v_code_1459_; 
v_code_1459_ = lean_ctor_get(v_alt_1431_, 1);
lean_inc_ref(v_code_1459_);
v___y_1439_ = v_code_1459_;
goto v___jp_1438_;
}
default: 
{
lean_object* v_code_1460_; 
v_code_1460_ = lean_ctor_get(v_alt_1431_, 0);
lean_inc_ref(v_code_1460_);
v___y_1439_ = v_code_1460_;
goto v___jp_1438_;
}
}
v___jp_1438_:
{
lean_object* v___x_1440_; 
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
v___x_1440_ = lean_apply_6(v_f_1432_, v___y_1439_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, lean_box(0));
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1449_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1431_, v_a_1441_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1445_);
v___x_1447_ = v___x_1443_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v_alt_1431_);
v_a_1450_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1440_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1440_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_1431_ = stack[0].m_obj;
lean_object* v_f_1432_ = stack[1].m_obj;
lean_object* v___y_1433_ = stack[2].m_obj;
lean_object* v___y_1434_ = stack[3].m_obj;
lean_object* v___y_1435_ = stack[4].m_obj;
lean_object* v___y_1436_ = stack[5].m_obj;
lean_object* v_res_1461_;
v_res_1461_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1431_, v_f_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
stack->m_obj
 = v_res_1461_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(lean_object* v_alt_1462_, lean_object* v_f_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1462_, v_f_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
return v_res_1469_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(uint8_t v_pu_1470_, lean_object* v_alt_1471_, lean_object* v_f_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1471_, v_f_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
return v___x_1478_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1470_ = stack[0].m_num;
lean_object* v_alt_1471_ = stack[1].m_obj;
lean_object* v_f_1472_ = stack[2].m_obj;
lean_object* v___y_1473_ = stack[3].m_obj;
lean_object* v___y_1474_ = stack[4].m_obj;
lean_object* v___y_1475_ = stack[5].m_obj;
lean_object* v___y_1476_ = stack[6].m_obj;
lean_object* v_res_1479_;
v_res_1479_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(v_pu_1470_, v_alt_1471_, v_f_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
stack->m_obj
 = v_res_1479_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(lean_object* v_pu_1480_, lean_object* v_alt_1481_, lean_object* v_f_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
uint8_t v_pu_boxed_1488_; lean_object* v_res_1489_; 
v_pu_boxed_1488_ = lean_unbox(v_pu_1480_);
v_res_1489_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(v_pu_boxed_1488_, v_alt_1481_, v_f_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1489_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1490_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object* v_msg_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_toApplicative_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1532_; 
v___x_1497_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_1498_ = l_StateRefT_x27_instMonad___redArg(v___x_1497_);
v_toApplicative_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v___x_1498_, 1);
lean_dec(v_unused_1533_);
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1532_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_toApplicative_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1532_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_toFunctor_1503_; lean_object* v_toSeq_1504_; lean_object* v_toSeqLeft_1505_; lean_object* v_toSeqRight_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1530_; 
v_toFunctor_1503_ = lean_ctor_get(v_toApplicative_1499_, 0);
v_toSeq_1504_ = lean_ctor_get(v_toApplicative_1499_, 2);
v_toSeqLeft_1505_ = lean_ctor_get(v_toApplicative_1499_, 3);
v_toSeqRight_1506_ = lean_ctor_get(v_toApplicative_1499_, 4);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_toApplicative_1499_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_toApplicative_1499_, 1);
lean_dec(v_unused_1531_);
v___x_1508_ = v_toApplicative_1499_;
v_isShared_1509_ = v_isSharedCheck_1530_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_toSeqRight_1506_);
lean_inc(v_toSeqLeft_1505_);
lean_inc(v_toSeq_1504_);
lean_inc(v_toFunctor_1503_);
lean_dec(v_toApplicative_1499_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1530_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___f_1510_; lean_object* v___f_1511_; lean_object* v___f_1512_; lean_object* v___f_1513_; lean_object* v___x_1514_; lean_object* v___f_1515_; lean_object* v___f_1516_; lean_object* v___f_1517_; lean_object* v___x_1519_; 
v___f_1510_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_1511_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1503_);
v___f_1512_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1512_, 0, v_toFunctor_1503_);
v___f_1513_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1513_, 0, v_toFunctor_1503_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___f_1512_);
lean_ctor_set(v___x_1514_, 1, v___f_1513_);
v___f_1515_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1515_, 0, v_toSeqRight_1506_);
v___f_1516_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1516_, 0, v_toSeqLeft_1505_);
v___f_1517_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1517_, 0, v_toSeq_1504_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v___f_1515_);
lean_ctor_set(v___x_1508_, 3, v___f_1516_);
lean_ctor_set(v___x_1508_, 2, v___f_1517_);
lean_ctor_set(v___x_1508_, 1, v___f_1510_);
lean_ctor_set(v___x_1508_, 0, v___x_1514_);
v___x_1519_ = v___x_1508_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___f_1510_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v___f_1517_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v___f_1516_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v___f_1515_);
v___x_1519_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 1, v___f_1511_);
lean_ctor_set(v___x_1501_, 0, v___x_1519_);
v___x_1521_ = v___x_1501_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___f_1511_);
v___x_1521_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___f_1525_; lean_object* v___x_6385__overap_1526_; lean_object* v___x_1527_; 
v___x_1522_ = l_StateRefT_x27_instMonad___redArg(v___x_1521_);
v___x_1523_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0);
v___x_1524_ = l_instInhabitedOfMonad___redArg(v___x_1522_, v___x_1523_);
v___f_1525_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1525_, 0, v___x_1524_);
v___x_6385__overap_1526_ = lean_panic_fn_borrowed(v___f_1525_, v_msg_1491_);
lean_dec_ref(v___f_1525_);
lean_inc(v___y_1495_);
lean_inc_ref(v___y_1494_);
lean_inc(v___y_1493_);
lean_inc_ref(v___y_1492_);
v___x_1527_ = lean_apply_5(v___x_6385__overap_1526_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, lean_box(0));
return v___x_1527_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1491_ = stack[0].m_obj;
lean_object* v___y_1492_ = stack[1].m_obj;
lean_object* v___y_1493_ = stack[2].m_obj;
lean_object* v___y_1494_ = stack[3].m_obj;
lean_object* v___y_1495_ = stack[4].m_obj;
lean_object* v_res_1534_;
v_res_1534_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v_msg_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
stack->m_obj
 = v_res_1534_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object* v_msg_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v_msg_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1541_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3));
v___x_1550_ = l_Lean_Expr_const___override(v___x_1549_, v___x_1548_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object* v_resetTokenId_1551_, lean_object* v_origAllocId_1552_, lean_object* v_isSharedId_1553_, lean_object* v_resultType_1554_, lean_object* v_x_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(v_resetTokenId_1551_, v_origAllocId_1552_, v_isSharedId_1553_, v_resultType_1554_, v_x_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1561_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object* v_resetTokenId_1562_, lean_object* v_origAllocId_1563_, lean_object* v_isSharedId_1564_, lean_object* v_resultType_1565_, lean_object* v_i_1566_, lean_object* v_as_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = lean_array_get_size(v_as_1567_);
v___x_1574_ = lean_nat_dec_lt(v_i_1566_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; 
lean_dec(v_i_1566_);
lean_dec_ref(v_resultType_1565_);
lean_dec(v_isSharedId_1564_);
lean_dec(v_origAllocId_1563_);
lean_dec(v_resetTokenId_1562_);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_as_1567_);
return v___x_1575_;
}
else
{
lean_object* v___f_1576_; lean_object* v_a_1577_; lean_object* v___x_1578_; 
lean_inc_ref(v_resultType_1565_);
lean_inc(v_isSharedId_1564_);
lean_inc(v_origAllocId_1563_);
lean_inc(v_resetTokenId_1562_);
v___f_1576_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1576_, 0, v_resetTokenId_1562_);
lean_closure_set(v___f_1576_, 1, v_origAllocId_1563_);
lean_closure_set(v___f_1576_, 2, v_isSharedId_1564_);
lean_closure_set(v___f_1576_, 3, v_resultType_1565_);
v_a_1577_ = lean_array_fget_borrowed(v_as_1567_, v_i_1566_);
lean_inc(v_a_1577_);
v___x_1578_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_1577_, v___f_1576_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; size_t v___x_1580_; size_t v___x_1581_; uint8_t v___x_1582_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1580_ = lean_ptr_addr(v_a_1577_);
v___x_1581_ = lean_ptr_addr(v_a_1579_);
v___x_1582_ = lean_usize_dec_eq(v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = lean_unsigned_to_nat(1u);
v___x_1584_ = lean_nat_add(v_i_1566_, v___x_1583_);
v___x_1585_ = lean_array_fset(v_as_1567_, v_i_1566_, v_a_1579_);
lean_dec(v_i_1566_);
v_i_1566_ = v___x_1584_;
v_as_1567_ = v___x_1585_;
goto _start;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec(v_a_1579_);
v___x_1587_ = lean_unsigned_to_nat(1u);
v___x_1588_ = lean_nat_add(v_i_1566_, v___x_1587_);
lean_dec(v_i_1566_);
v_i_1566_ = v___x_1588_;
goto _start;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v_as_1567_);
lean_dec(v_i_1566_);
lean_dec_ref(v_resultType_1565_);
lean_dec(v_isSharedId_1564_);
lean_dec(v_origAllocId_1563_);
lean_dec(v_resetTokenId_1562_);
v_a_1590_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1578_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1578_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_resetTokenId_1562_ = stack[0].m_obj;
lean_object* v_origAllocId_1563_ = stack[1].m_obj;
lean_object* v_isSharedId_1564_ = stack[2].m_obj;
lean_object* v_resultType_1565_ = stack[3].m_obj;
lean_object* v_i_1566_ = stack[4].m_obj;
lean_object* v_as_1567_ = stack[5].m_obj;
lean_object* v___y_1568_ = stack[6].m_obj;
lean_object* v___y_1569_ = stack[7].m_obj;
lean_object* v___y_1570_ = stack[8].m_obj;
lean_object* v___y_1571_ = stack[9].m_obj;
lean_object* v_res_1598_;
v_res_1598_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_1562_, v_origAllocId_1563_, v_isSharedId_1564_, v_resultType_1565_, v_i_1566_, v_as_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
stack->m_obj
 = v_res_1598_;
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1601_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6));
v___x_1602_ = lean_unsigned_to_nat(6u);
v___x_1603_ = lean_unsigned_to_nat(208u);
v___x_1604_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5));
v___x_1605_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_1606_ = l_mkPanicMessageWithDecl(v___x_1605_, v___x_1604_, v___x_1603_, v___x_1602_, v___x_1601_);
return v___x_1606_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object* v_resetTokenId_1607_, lean_object* v_code_1608_, lean_object* v_origAllocId_1609_, lean_object* v_isSharedId_1610_, lean_object* v_currentRetType_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
switch(lean_obj_tag(v_code_1608_))
{
case 0:
{
lean_object* v_decl_1617_; lean_object* v_value_1618_; 
v_decl_1617_ = lean_ctor_get(v_code_1608_, 0);
v_value_1618_ = lean_ctor_get(v_decl_1617_, 3);
lean_inc(v_value_1618_);
if (lean_obj_tag(v_value_1618_) == 12)
{
lean_object* v_k_1619_; lean_object* v_fvarId_1620_; lean_object* v_binderName_1621_; lean_object* v_type_1622_; lean_object* v_var_1623_; lean_object* v_i_1624_; uint8_t v_updateHeader_1625_; lean_object* v_args_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1742_; 
v_k_1619_ = lean_ctor_get(v_code_1608_, 1);
v_fvarId_1620_ = lean_ctor_get(v_decl_1617_, 0);
v_binderName_1621_ = lean_ctor_get(v_decl_1617_, 1);
v_type_1622_ = lean_ctor_get(v_decl_1617_, 2);
v_var_1623_ = lean_ctor_get(v_value_1618_, 0);
v_i_1624_ = lean_ctor_get(v_value_1618_, 1);
v_updateHeader_1625_ = lean_ctor_get_uint8(v_value_1618_, sizeof(void*)*3);
v_args_1626_ = lean_ctor_get(v_value_1618_, 2);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_value_1618_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1628_ = v_value_1618_;
v_isShared_1629_ = v_isSharedCheck_1742_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_args_1626_);
lean_inc(v_i_1624_);
lean_inc(v_var_1623_);
lean_dec(v_value_1618_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1742_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
uint8_t v___x_1630_; 
v___x_1630_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1607_, v_var_1623_);
lean_dec(v_var_1623_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
lean_del_object(v___x_1628_);
lean_dec_ref(v_args_1626_);
lean_dec_ref(v_i_1624_);
lean_inc_ref(v_k_1619_);
v___x_1631_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_k_1619_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1654_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1654_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1654_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
size_t v___x_1636_; size_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1636_ = lean_ptr_addr(v_k_1619_);
v___x_1637_ = lean_ptr_addr(v_a_1632_);
v___x_1638_ = lean_usize_dec_eq(v___x_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1648_; 
lean_inc_ref(v_decl_1617_);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; lean_object* v_unused_1650_; 
v_unused_1649_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_1650_);
v___x_1640_ = v_code_1608_;
v_isShared_1641_ = v_isSharedCheck_1648_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v_code_1608_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1648_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v_a_1632_);
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_decl_1617_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_a_1632_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1643_);
v___x_1645_ = v___x_1634_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v___x_1652_; 
lean_dec(v_a_1632_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v_code_1608_);
v___x_1652_ = v___x_1634_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_code_1608_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1608_, 2);
return v___x_1631_;
}
}
else
{
lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1739_; 
lean_inc_ref(v_k_1619_);
lean_inc_ref(v_decl_1617_);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; lean_object* v_unused_1741_; 
v_unused_1740_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_1740_);
v_unused_1741_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_1741_);
v___x_1656_ = v_code_1608_;
v_isShared_1657_ = v_isSharedCheck_1739_;
goto v_resetjp_1655_;
}
else
{
lean_dec(v_code_1608_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1739_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
uint8_t v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = 0;
v___x_1659_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_fvarId_1620_, v_k_1619_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v_fst_1661_; lean_object* v_snd_1662_; lean_object* v___x_1663_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v_fst_1661_ = lean_ctor_get(v_a_1660_, 0);
lean_inc(v_fst_1661_);
v_snd_1662_ = lean_ctor_get(v_a_1660_, 1);
lean_inc(v_snd_1662_);
lean_dec(v_a_1660_);
v___x_1663_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_origAllocId_1609_, v_fst_1661_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
lean_dec(v_fst_1661_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v_fst_1665_; lean_object* v_snd_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v_fst_1665_ = lean_ctor_get(v_a_1664_, 0);
lean_inc(v_fst_1665_);
v_snd_1666_ = lean_ctor_get(v_a_1664_, 1);
lean_inc(v_snd_1666_);
lean_dec(v_a_1664_);
v___x_1667_ = 1;
v___x_1668_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_1666_, v_snd_1662_);
lean_dec(v_snd_1666_);
lean_inc_ref(v_type_1622_);
lean_inc(v_binderName_1621_);
lean_inc(v_fvarId_1620_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 0);
lean_ctor_set(v___x_1628_, 2, v_type_1622_);
lean_ctor_set(v___x_1628_, 1, v_binderName_1621_);
lean_ctor_set(v___x_1628_, 0, v_fvarId_1620_);
v___x_1670_ = v___x_1628_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_fvarId_1620_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_binderName_1621_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_type_1622_);
v___x_1670_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*3, v___x_1658_);
v___x_1671_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1));
v___x_1672_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1671_, v_a_1613_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1674_ = lean_unsigned_to_nat(1u);
v___x_1675_ = lean_mk_empty_array_with_capacity(v___x_1674_);
v___x_1676_ = lean_array_push(v___x_1675_, v___x_1670_);
lean_inc_ref(v_currentRetType_1611_);
v___x_1677_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_1667_, v_a_1673_, v_currentRetType_1611_, v___x_1676_, v___x_1668_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v_fvarId_1679_; lean_object* v___x_1680_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1677_, 1);
v_fvarId_1679_ = lean_ctor_get(v_a_1678_, 0);
lean_inc(v_fvarId_1679_);
lean_inc_ref(v_args_1626_);
lean_inc_ref(v_i_1624_);
lean_inc_ref(v_decl_1617_);
v___x_1680_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1617_, v_i_1624_, v_args_1626_, v_fvarId_1679_, v_fst_1665_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1682_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
lean_inc(v_fvarId_1679_);
v___x_1682_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1607_, v_i_1624_, v_updateHeader_1625_, v_args_1626_, v_fvarId_1679_, v_origAllocId_1609_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
lean_dec(v_origAllocId_1609_);
lean_dec_ref(v_args_1626_);
lean_dec_ref(v_i_1624_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1684_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1682_, 1);
v___x_1684_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_1667_, v_decl_1617_, v_a_1613_);
lean_dec_ref(v_decl_1617_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec_ref_known(v___x_1684_, 1);
v___x_1685_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_1686_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_isSharedId_1610_, v___x_1685_, v_currentRetType_1611_, v_a_1681_, v_a_1683_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1697_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1697_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1697_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set_tag(v___x_1656_, 2);
lean_ctor_set(v___x_1656_, 1, v_a_1687_);
lean_ctor_set(v___x_1656_, 0, v_a_1678_);
v___x_1692_ = v___x_1656_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1678_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1694_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1692_);
v___x_1694_ = v___x_1689_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_dec(v_a_1678_);
lean_del_object(v___x_1656_);
return v___x_1686_;
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_a_1683_);
lean_dec(v_a_1681_);
lean_dec(v_a_1678_);
lean_del_object(v___x_1656_);
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
v_a_1698_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1684_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1684_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
lean_dec(v_a_1681_);
lean_dec(v_a_1678_);
lean_del_object(v___x_1656_);
lean_dec_ref(v_decl_1617_);
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
return v___x_1682_;
}
}
else
{
lean_dec(v_a_1678_);
lean_del_object(v___x_1656_);
lean_dec_ref(v_args_1626_);
lean_dec_ref(v_i_1624_);
lean_dec_ref(v_decl_1617_);
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
lean_dec(v_origAllocId_1609_);
lean_dec(v_resetTokenId_1607_);
return v___x_1680_;
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec(v_fst_1665_);
lean_del_object(v___x_1656_);
lean_dec_ref(v_args_1626_);
lean_dec_ref(v_i_1624_);
lean_dec_ref(v_decl_1617_);
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
lean_dec(v_origAllocId_1609_);
lean_dec(v_resetTokenId_1607_);
v_a_1706_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1677_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1677_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v___x_1670_);
lean_dec_ref(v___x_1668_);
lean_dec(v_fst_1665_);
lean_del_object(v___x_1656_);
lean_dec_ref(v_args_1626_);
lean_dec_ref(v_i_1624_);
lean_dec_ref(v_decl_1617_);
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
lean_dec(v_origAllocId_1609_);
lean_dec(v_resetTokenId_1607_);
v_a_1714_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1672_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1672_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_snd_1662_);
lean_del_object(v___x_1656_);
lean_del_object(v___x_1628_);
lean_dec_ref(v_args_1626_);
lean_dec_ref(v_i_1624_);
lean_dec_ref(v_decl_1617_);
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
lean_dec(v_origAllocId_1609_);
lean_dec(v_resetTokenId_1607_);
v_a_1723_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1663_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1663_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_del_object(v___x_1656_);
lean_del_object(v___x_1628_);
lean_dec_ref(v_args_1626_);
lean_dec_ref(v_i_1624_);
lean_dec_ref(v_decl_1617_);
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
lean_dec(v_origAllocId_1609_);
lean_dec(v_resetTokenId_1607_);
v_a_1731_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1659_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1659_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
}
}
else
{
lean_object* v_k_1743_; lean_object* v___x_1744_; 
lean_dec(v_value_1618_);
v_k_1743_ = lean_ctor_get(v_code_1608_, 1);
lean_inc_ref(v_k_1743_);
v___x_1744_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_k_1743_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1767_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1767_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1767_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
size_t v___x_1749_; size_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1749_ = lean_ptr_addr(v_k_1743_);
v___x_1750_ = lean_ptr_addr(v_a_1745_);
v___x_1751_ = lean_usize_dec_eq(v___x_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1761_; 
lean_inc_ref(v_decl_1617_);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; lean_object* v_unused_1763_; 
v_unused_1762_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_1762_);
v_unused_1763_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_1763_);
v___x_1753_ = v_code_1608_;
v_isShared_1754_ = v_isSharedCheck_1761_;
goto v_resetjp_1752_;
}
else
{
lean_dec(v_code_1608_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1761_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 1, v_a_1745_);
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_decl_1617_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_a_1745_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1756_);
v___x_1758_ = v___x_1747_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v___x_1765_; 
lean_dec(v_a_1745_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v_code_1608_);
v___x_1765_ = v___x_1747_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_code_1608_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1608_, 2);
return v___x_1744_;
}
}
}
case 2:
{
lean_object* v_decl_1768_; lean_object* v_k_1769_; lean_object* v_params_1770_; lean_object* v_type_1771_; lean_object* v_value_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; 
v_decl_1768_ = lean_ctor_get(v_code_1608_, 0);
v_k_1769_ = lean_ctor_get(v_code_1608_, 1);
v_params_1770_ = lean_ctor_get(v_decl_1768_, 2);
v_type_1771_ = lean_ctor_get(v_decl_1768_, 3);
v_value_1772_ = lean_ctor_get(v_decl_1768_, 4);
v___x_1773_ = 1;
lean_inc_ref(v_type_1771_);
lean_inc(v_isSharedId_1610_);
lean_inc(v_origAllocId_1609_);
lean_inc_ref(v_value_1772_);
lean_inc(v_resetTokenId_1607_);
v___x_1774_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_value_1772_, v_origAllocId_1609_, v_isSharedId_1610_, v_type_1771_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
lean_inc_ref(v_params_1770_);
lean_inc_ref(v_type_1771_);
lean_inc_ref(v_decl_1768_);
v___x_1776_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1773_, v_decl_1768_, v_type_1771_, v_params_1770_, v_a_1775_, v_a_1613_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
lean_inc_ref(v_k_1769_);
v___x_1778_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_k_1769_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1816_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1816_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1816_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
size_t v___x_1783_; size_t v___x_1784_; uint8_t v___x_1785_; 
v___x_1783_ = lean_ptr_addr(v_k_1769_);
v___x_1784_ = lean_ptr_addr(v_a_1779_);
v___x_1785_ = lean_usize_dec_eq(v___x_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1795_; 
v_isSharedCheck_1795_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; lean_object* v_unused_1797_; 
v_unused_1796_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_1796_);
v_unused_1797_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_1797_);
v___x_1787_ = v_code_1608_;
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
else
{
lean_dec(v_code_1608_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v_a_1779_);
lean_ctor_set(v___x_1787_, 0, v_a_1777_);
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1777_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_a_1779_);
v___x_1790_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1792_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1790_);
v___x_1792_ = v___x_1781_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
size_t v___x_1798_; size_t v___x_1799_; uint8_t v___x_1800_; 
v___x_1798_ = lean_ptr_addr(v_decl_1768_);
v___x_1799_ = lean_ptr_addr(v_a_1777_);
v___x_1800_ = lean_usize_dec_eq(v___x_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1810_; 
v_isSharedCheck_1810_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; lean_object* v_unused_1812_; 
v_unused_1811_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_1811_);
v_unused_1812_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_1812_);
v___x_1802_ = v_code_1608_;
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
else
{
lean_dec(v_code_1608_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v_a_1779_);
lean_ctor_set(v___x_1802_, 0, v_a_1777_);
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1777_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_a_1779_);
v___x_1805_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1807_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1805_);
v___x_1807_ = v___x_1781_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v___x_1814_; 
lean_dec(v_a_1779_);
lean_dec(v_a_1777_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v_code_1608_);
v___x_1814_ = v___x_1781_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_code_1608_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
else
{
lean_dec(v_a_1777_);
lean_dec_ref_known(v_code_1608_, 2);
return v___x_1778_;
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref_known(v_code_1608_, 2);
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
lean_dec(v_origAllocId_1609_);
lean_dec(v_resetTokenId_1607_);
v_a_1817_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1776_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1776_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1608_, 2);
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
lean_dec(v_origAllocId_1609_);
lean_dec(v_resetTokenId_1607_);
return v___x_1774_;
}
}
case 4:
{
lean_object* v_cases_1825_; lean_object* v_typeName_1826_; lean_object* v_resultType_1827_; lean_object* v_discr_1828_; lean_object* v_alts_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_currentRetType_1611_);
v_cases_1825_ = lean_ctor_get(v_code_1608_, 0);
lean_inc_ref(v_cases_1825_);
v_typeName_1826_ = lean_ctor_get(v_cases_1825_, 0);
v_resultType_1827_ = lean_ctor_get(v_cases_1825_, 1);
v_discr_1828_ = lean_ctor_get(v_cases_1825_, 2);
v_alts_1829_ = lean_ctor_get(v_cases_1825_, 3);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_cases_1825_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1831_ = v_cases_1825_;
v_isShared_1832_ = v_isSharedCheck_1868_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_alts_1829_);
lean_inc(v_discr_1828_);
lean_inc(v_resultType_1827_);
lean_inc(v_typeName_1826_);
lean_dec(v_cases_1825_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1868_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1829_);
lean_inc_ref(v_resultType_1827_);
v___x_1834_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_1607_, v_origAllocId_1609_, v_isSharedId_1610_, v_resultType_1827_, v___x_1833_, v_alts_1829_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1859_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1859_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1859_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
size_t v___x_1839_; size_t v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = lean_ptr_addr(v_alts_1829_);
lean_dec_ref(v_alts_1829_);
v___x_1840_ = lean_ptr_addr(v_a_1835_);
v___x_1841_ = lean_usize_dec_eq(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1854_; 
v_isSharedCheck_1854_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_1855_);
v___x_1843_ = v_code_1608_;
v_isShared_1844_ = v_isSharedCheck_1854_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v_code_1608_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1854_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 3, v_a_1835_);
v___x_1846_ = v___x_1831_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_typeName_1826_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_resultType_1827_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_discr_1828_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_a_1835_);
v___x_1846_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1846_);
v___x_1848_ = v___x_1843_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1850_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1848_);
v___x_1850_ = v___x_1837_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
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
}
}
else
{
lean_object* v___x_1857_; 
lean_dec(v_a_1835_);
lean_del_object(v___x_1831_);
lean_dec(v_discr_1828_);
lean_dec_ref(v_resultType_1827_);
lean_dec(v_typeName_1826_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v_code_1608_);
v___x_1857_ = v___x_1837_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_code_1608_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1831_);
lean_dec_ref(v_alts_1829_);
lean_dec(v_discr_1828_);
lean_dec_ref(v_resultType_1827_);
lean_dec(v_typeName_1826_);
lean_dec_ref_known(v_code_1608_, 1);
v_a_1860_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1834_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1834_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1869_; lean_object* v_i_1870_; lean_object* v_y_1871_; lean_object* v_k_1872_; lean_object* v___x_1873_; 
v_fvarId_1869_ = lean_ctor_get(v_code_1608_, 0);
v_i_1870_ = lean_ctor_get(v_code_1608_, 1);
v_y_1871_ = lean_ctor_get(v_code_1608_, 2);
v_k_1872_ = lean_ctor_get(v_code_1608_, 3);
lean_inc_ref(v_k_1872_);
v___x_1873_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_k_1872_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1898_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1898_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1898_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
size_t v___x_1878_; size_t v___x_1879_; uint8_t v___x_1880_; 
v___x_1878_ = lean_ptr_addr(v_k_1872_);
v___x_1879_ = lean_ptr_addr(v_a_1874_);
v___x_1880_ = lean_usize_dec_eq(v___x_1878_, v___x_1879_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1890_; 
lean_inc(v_y_1871_);
lean_inc(v_i_1870_);
lean_inc(v_fvarId_1869_);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; lean_object* v_unused_1892_; lean_object* v_unused_1893_; lean_object* v_unused_1894_; 
v_unused_1891_ = lean_ctor_get(v_code_1608_, 3);
lean_dec(v_unused_1891_);
v_unused_1892_ = lean_ctor_get(v_code_1608_, 2);
lean_dec(v_unused_1892_);
v_unused_1893_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_1893_);
v_unused_1894_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_1894_);
v___x_1882_ = v_code_1608_;
v_isShared_1883_ = v_isSharedCheck_1890_;
goto v_resetjp_1881_;
}
else
{
lean_dec(v_code_1608_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1890_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 3, v_a_1874_);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_fvarId_1869_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_i_1870_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_y_1871_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_a_1874_);
v___x_1885_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1885_);
v___x_1887_ = v___x_1876_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v___x_1896_; 
lean_dec(v_a_1874_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v_code_1608_);
v___x_1896_ = v___x_1876_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_code_1608_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1608_, 4);
return v___x_1873_;
}
}
case 8:
{
lean_object* v_fvarId_1899_; lean_object* v_i_1900_; lean_object* v_y_1901_; lean_object* v_k_1902_; lean_object* v___x_1903_; 
v_fvarId_1899_ = lean_ctor_get(v_code_1608_, 0);
v_i_1900_ = lean_ctor_get(v_code_1608_, 1);
v_y_1901_ = lean_ctor_get(v_code_1608_, 2);
v_k_1902_ = lean_ctor_get(v_code_1608_, 3);
lean_inc_ref(v_k_1902_);
v___x_1903_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_k_1902_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1928_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1928_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1928_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
size_t v___x_1908_; size_t v___x_1909_; uint8_t v___x_1910_; 
v___x_1908_ = lean_ptr_addr(v_k_1902_);
v___x_1909_ = lean_ptr_addr(v_a_1904_);
v___x_1910_ = lean_usize_dec_eq(v___x_1908_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1920_; 
lean_inc(v_y_1901_);
lean_inc(v_i_1900_);
lean_inc(v_fvarId_1899_);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; lean_object* v_unused_1922_; lean_object* v_unused_1923_; lean_object* v_unused_1924_; 
v_unused_1921_ = lean_ctor_get(v_code_1608_, 3);
lean_dec(v_unused_1921_);
v_unused_1922_ = lean_ctor_get(v_code_1608_, 2);
lean_dec(v_unused_1922_);
v_unused_1923_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_1924_);
v___x_1912_ = v_code_1608_;
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
else
{
lean_dec(v_code_1608_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 3, v_a_1904_);
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_fvarId_1899_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_i_1900_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_y_1901_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_a_1904_);
v___x_1915_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1915_);
v___x_1917_ = v___x_1906_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v___x_1926_; 
lean_dec(v_a_1904_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v_code_1608_);
v___x_1926_ = v___x_1906_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_code_1608_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1608_, 4);
return v___x_1903_;
}
}
case 9:
{
lean_object* v_fvarId_1929_; lean_object* v_i_1930_; lean_object* v_offset_1931_; lean_object* v_y_1932_; lean_object* v_ty_1933_; lean_object* v_k_1934_; lean_object* v___x_1935_; 
v_fvarId_1929_ = lean_ctor_get(v_code_1608_, 0);
v_i_1930_ = lean_ctor_get(v_code_1608_, 1);
v_offset_1931_ = lean_ctor_get(v_code_1608_, 2);
v_y_1932_ = lean_ctor_get(v_code_1608_, 3);
v_ty_1933_ = lean_ctor_get(v_code_1608_, 4);
v_k_1934_ = lean_ctor_get(v_code_1608_, 5);
lean_inc_ref(v_k_1934_);
v___x_1935_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_k_1934_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1962_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1962_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1962_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
size_t v___x_1940_; size_t v___x_1941_; uint8_t v___x_1942_; 
v___x_1940_ = lean_ptr_addr(v_k_1934_);
v___x_1941_ = lean_ptr_addr(v_a_1936_);
v___x_1942_ = lean_usize_dec_eq(v___x_1940_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1952_; 
lean_inc_ref(v_ty_1933_);
lean_inc(v_y_1932_);
lean_inc(v_offset_1931_);
lean_inc(v_i_1930_);
lean_inc(v_fvarId_1929_);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; lean_object* v_unused_1954_; lean_object* v_unused_1955_; lean_object* v_unused_1956_; lean_object* v_unused_1957_; lean_object* v_unused_1958_; 
v_unused_1953_ = lean_ctor_get(v_code_1608_, 5);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_code_1608_, 4);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_code_1608_, 3);
lean_dec(v_unused_1955_);
v_unused_1956_ = lean_ctor_get(v_code_1608_, 2);
lean_dec(v_unused_1956_);
v_unused_1957_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_1957_);
v_unused_1958_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_1958_);
v___x_1944_ = v_code_1608_;
v_isShared_1945_ = v_isSharedCheck_1952_;
goto v_resetjp_1943_;
}
else
{
lean_dec(v_code_1608_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1952_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 5, v_a_1936_);
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_fvarId_1929_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_i_1930_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_offset_1931_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_y_1932_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v_ty_1933_);
lean_ctor_set(v_reuseFailAlloc_1951_, 5, v_a_1936_);
v___x_1947_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1949_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1947_);
v___x_1949_ = v___x_1938_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_object* v___x_1960_; 
lean_dec(v_a_1936_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v_code_1608_);
v___x_1960_ = v___x_1938_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_code_1608_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1608_, 6);
return v___x_1935_;
}
}
case 10:
{
lean_object* v_fvarId_1963_; lean_object* v_cidx_1964_; lean_object* v_k_1965_; lean_object* v___x_1966_; 
v_fvarId_1963_ = lean_ctor_get(v_code_1608_, 0);
v_cidx_1964_ = lean_ctor_get(v_code_1608_, 1);
v_k_1965_ = lean_ctor_get(v_code_1608_, 2);
lean_inc_ref(v_k_1965_);
v___x_1966_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_k_1965_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1990_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1990_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1990_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
size_t v___x_1971_; size_t v___x_1972_; uint8_t v___x_1973_; 
v___x_1971_ = lean_ptr_addr(v_k_1965_);
v___x_1972_ = lean_ptr_addr(v_a_1967_);
v___x_1973_ = lean_usize_dec_eq(v___x_1971_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1983_; 
lean_inc(v_cidx_1964_);
lean_inc(v_fvarId_1963_);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; lean_object* v_unused_1985_; lean_object* v_unused_1986_; 
v_unused_1984_ = lean_ctor_get(v_code_1608_, 2);
lean_dec(v_unused_1984_);
v_unused_1985_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_1985_);
v_unused_1986_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_1986_);
v___x_1975_ = v_code_1608_;
v_isShared_1976_ = v_isSharedCheck_1983_;
goto v_resetjp_1974_;
}
else
{
lean_dec(v_code_1608_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1983_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 2, v_a_1967_);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_fvarId_1963_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_cidx_1964_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_a_1967_);
v___x_1978_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1980_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1978_);
v___x_1980_ = v___x_1969_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v___x_1988_; 
lean_dec(v_a_1967_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v_code_1608_);
v___x_1988_ = v___x_1969_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_code_1608_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1608_, 3);
return v___x_1966_;
}
}
case 11:
{
lean_object* v_fvarId_1991_; lean_object* v_n_1992_; uint8_t v_check_1993_; uint8_t v_persistent_1994_; lean_object* v_k_1995_; lean_object* v___x_1996_; 
v_fvarId_1991_ = lean_ctor_get(v_code_1608_, 0);
v_n_1992_ = lean_ctor_get(v_code_1608_, 1);
v_check_1993_ = lean_ctor_get_uint8(v_code_1608_, sizeof(void*)*3);
v_persistent_1994_ = lean_ctor_get_uint8(v_code_1608_, sizeof(void*)*3 + 1);
v_k_1995_ = lean_ctor_get(v_code_1608_, 2);
lean_inc_ref(v_k_1995_);
v___x_1996_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_k_1995_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2020_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2020_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2020_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
size_t v___x_2001_; size_t v___x_2002_; uint8_t v___x_2003_; 
v___x_2001_ = lean_ptr_addr(v_k_1995_);
v___x_2002_ = lean_ptr_addr(v_a_1997_);
v___x_2003_ = lean_usize_dec_eq(v___x_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2013_; 
lean_inc(v_n_1992_);
lean_inc(v_fvarId_1991_);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; lean_object* v_unused_2015_; lean_object* v_unused_2016_; 
v_unused_2014_ = lean_ctor_get(v_code_1608_, 2);
lean_dec(v_unused_2014_);
v_unused_2015_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_2015_);
v_unused_2016_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_2016_);
v___x_2005_ = v_code_1608_;
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
else
{
lean_dec(v_code_1608_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 2, v_a_1997_);
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_fvarId_1991_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_n_1992_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_a_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, sizeof(void*)*3, v_check_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, sizeof(void*)*3 + 1, v_persistent_1994_);
v___x_2008_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2008_);
v___x_2010_ = v___x_1999_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v___x_2018_; 
lean_dec(v_a_1997_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v_code_1608_);
v___x_2018_ = v___x_1999_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_code_1608_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1608_, 3);
return v___x_1996_;
}
}
case 12:
{
lean_object* v_fvarId_2021_; lean_object* v_n_2022_; uint8_t v_check_2023_; uint8_t v_persistent_2024_; lean_object* v_objs_x3f_2025_; lean_object* v_k_2026_; uint8_t v___x_2027_; 
v_fvarId_2021_ = lean_ctor_get(v_code_1608_, 0);
v_n_2022_ = lean_ctor_get(v_code_1608_, 1);
v_check_2023_ = lean_ctor_get_uint8(v_code_1608_, sizeof(void*)*4);
v_persistent_2024_ = lean_ctor_get_uint8(v_code_1608_, sizeof(void*)*4 + 1);
v_objs_x3f_2025_ = lean_ctor_get(v_code_1608_, 2);
v_k_2026_ = lean_ctor_get(v_code_1608_, 3);
v___x_2027_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1607_, v_fvarId_2021_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; 
lean_inc_ref(v_k_2026_);
v___x_2028_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_k_2026_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2053_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2053_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2053_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
size_t v___x_2033_; size_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = lean_ptr_addr(v_k_2026_);
v___x_2034_ = lean_ptr_addr(v_a_2029_);
v___x_2035_ = lean_usize_dec_eq(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2045_; 
lean_inc(v_objs_x3f_2025_);
lean_inc(v_n_2022_);
lean_inc(v_fvarId_2021_);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; lean_object* v_unused_2047_; lean_object* v_unused_2048_; lean_object* v_unused_2049_; 
v_unused_2046_ = lean_ctor_get(v_code_1608_, 3);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_code_1608_, 2);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_2049_);
v___x_2037_ = v_code_1608_;
v_isShared_2038_ = v_isSharedCheck_2045_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v_code_1608_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2045_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 3, v_a_2029_);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_fvarId_2021_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_n_2022_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_objs_x3f_2025_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_a_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*4, v_check_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*4 + 1, v_persistent_2024_);
v___x_2040_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2040_);
v___x_2042_ = v___x_2031_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v___x_2051_; 
lean_dec(v_a_2029_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v_code_1608_);
v___x_2051_ = v___x_2031_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_code_1608_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1608_, 4);
return v___x_2028_;
}
}
else
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
lean_inc_ref(v_k_2026_);
lean_inc(v_n_2022_);
lean_dec_ref_known(v_code_1608_, 4);
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
lean_dec(v_origAllocId_1609_);
v___x_2054_ = lean_unsigned_to_nat(1u);
v___x_2055_ = lean_nat_dec_eq(v_n_2022_, v___x_2054_);
lean_dec(v_n_2022_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec_ref(v_k_2026_);
lean_dec(v_resetTokenId_1607_);
v___x_2056_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7);
v___x_2057_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v___x_2056_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
return v___x_2057_;
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_2058_, 0, v_resetTokenId_1607_);
lean_ctor_set(v___x_2058_, 1, v_k_2026_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
}
}
case 13:
{
lean_object* v_fvarId_2060_; lean_object* v_k_2061_; lean_object* v___x_2062_; 
v_fvarId_2060_ = lean_ctor_get(v_code_1608_, 0);
v_k_2061_ = lean_ctor_get(v_code_1608_, 1);
lean_inc_ref(v_k_2061_);
v___x_2062_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_k_2061_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2085_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2085_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2085_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
size_t v___x_2067_; size_t v___x_2068_; uint8_t v___x_2069_; 
v___x_2067_ = lean_ptr_addr(v_k_2061_);
v___x_2068_ = lean_ptr_addr(v_a_2063_);
v___x_2069_ = lean_usize_dec_eq(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2079_; 
lean_inc(v_fvarId_2060_);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_code_1608_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; lean_object* v_unused_2081_; 
v_unused_2080_ = lean_ctor_get(v_code_1608_, 1);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v_code_1608_, 0);
lean_dec(v_unused_2081_);
v___x_2071_ = v_code_1608_;
v_isShared_2072_ = v_isSharedCheck_2079_;
goto v_resetjp_2070_;
}
else
{
lean_dec(v_code_1608_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2079_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v_a_2063_);
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_fvarId_2060_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_a_2063_);
v___x_2074_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2076_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2074_);
v___x_2076_ = v___x_2065_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v___x_2083_; 
lean_dec(v_a_2063_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v_code_1608_);
v___x_2083_ = v___x_2065_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_code_1608_);
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
else
{
lean_dec_ref_known(v_code_1608_, 2);
return v___x_2062_;
}
}
default: 
{
lean_object* v___x_2086_; 
lean_dec_ref(v_currentRetType_1611_);
lean_dec(v_isSharedId_1610_);
lean_dec(v_origAllocId_1609_);
lean_dec(v_resetTokenId_1607_);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_code_1608_);
return v___x_2086_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_0interp(lean_interpreter_value* stack)
{
lean_object* v_resetTokenId_1607_ = stack[0].m_obj;
lean_object* v_code_1608_ = stack[1].m_obj;
lean_object* v_origAllocId_1609_ = stack[2].m_obj;
lean_object* v_isSharedId_1610_ = stack[3].m_obj;
lean_object* v_currentRetType_1611_ = stack[4].m_obj;
lean_object* v_a_1612_ = stack[5].m_obj;
lean_object* v_a_1613_ = stack[6].m_obj;
lean_object* v_a_1614_ = stack[7].m_obj;
lean_object* v_a_1615_ = stack[8].m_obj;
lean_object* v_res_2087_;
v_res_2087_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1607_, v_code_1608_, v_origAllocId_1609_, v_isSharedId_1610_, v_currentRetType_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
stack->m_obj
 = v_res_2087_;
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object* v_resetTokenId_2088_, lean_object* v_origAllocId_2089_, lean_object* v_isSharedId_2090_, lean_object* v_resultType_2091_, lean_object* v_x_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2088_, v_x_2092_, v_origAllocId_2089_, v_isSharedId_2090_, v_resultType_2091_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_resetTokenId_2088_ = stack[0].m_obj;
lean_object* v_origAllocId_2089_ = stack[1].m_obj;
lean_object* v_isSharedId_2090_ = stack[2].m_obj;
lean_object* v_resultType_2091_ = stack[3].m_obj;
lean_object* v_x_2092_ = stack[4].m_obj;
lean_object* v___y_2093_ = stack[5].m_obj;
lean_object* v___y_2094_ = stack[6].m_obj;
lean_object* v___y_2095_ = stack[7].m_obj;
lean_object* v___y_2096_ = stack[8].m_obj;
lean_object* v_res_2099_;
v_res_2099_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(v_resetTokenId_2088_, v_origAllocId_2089_, v_isSharedId_2090_, v_resultType_2091_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
stack->m_obj
 = v_res_2099_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object* v_resetTokenId_2100_, lean_object* v_origAllocId_2101_, lean_object* v_isSharedId_2102_, lean_object* v_resultType_2103_, lean_object* v_i_2104_, lean_object* v_as_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_2100_, v_origAllocId_2101_, v_isSharedId_2102_, v_resultType_2103_, v_i_2104_, v_as_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object* v_resetTokenId_2112_, lean_object* v_code_2113_, lean_object* v_origAllocId_2114_, lean_object* v_isSharedId_2115_, lean_object* v_currentRetType_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2112_, v_code_2113_, v_origAllocId_2114_, v_isSharedId_2115_, v_currentRetType_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
return v_res_2122_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object* v_currentRetType_2132_, lean_object* v_ds_2133_, lean_object* v_decl_2134_, lean_object* v_nFields_2135_, lean_object* v_origAllocId_2136_, lean_object* v_k_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_2135_, v_origAllocId_2136_, v_ds_2133_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v_fst_2145_; lean_object* v_snd_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2267_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v_fst_2145_ = lean_ctor_get(v_a_2144_, 0);
v_snd_2146_ = lean_ctor_get(v_a_2144_, 1);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_a_2144_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2148_ = v_a_2144_;
v_isShared_2149_ = v_isSharedCheck_2267_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_snd_2146_);
lean_inc(v_fst_2145_);
lean_dec(v_a_2144_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2267_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1));
v___x_2151_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2150_, v_a_2139_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v___x_2153_ = 1;
v___x_2154_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_2155_ = 0;
v___x_2156_ = l_Lean_Compiler_LCNF_mkParam(v___x_2153_, v_a_2152_, v___x_2154_, v___x_2155_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v_fvarId_2158_; lean_object* v_binderName_2159_; lean_object* v_fvarId_2160_; lean_object* v___x_2161_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v_fvarId_2158_ = lean_ctor_get(v_decl_2134_, 0);
v_binderName_2159_ = lean_ctor_get(v_decl_2134_, 1);
v_fvarId_2160_ = lean_ctor_get(v_a_2157_, 0);
lean_inc_ref(v_currentRetType_2132_);
lean_inc(v_fvarId_2160_);
lean_inc(v_origAllocId_2136_);
lean_inc(v_fvarId_2158_);
v___x_2161_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_fvarId_2158_, v_k_2137_, v_origAllocId_2136_, v_fvarId_2160_, v_currentRetType_2132_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
v___x_2163_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_currentRetType_2132_);
v___x_2164_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_a_2162_, v___x_2163_, v_currentRetType_2132_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2250_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2250_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2250_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2169_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_binderName_2159_);
lean_inc(v_fvarId_2158_);
v___x_2170_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2170_, 0, v_fvarId_2158_);
lean_ctor_set(v___x_2170_, 1, v_binderName_2159_);
lean_ctor_set(v___x_2170_, 2, v___x_2169_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*3, v___x_2155_);
v___x_2171_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3));
v___x_2172_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2171_, v_a_2139_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = lean_unsigned_to_nat(2u);
v___x_2175_ = lean_mk_empty_array_with_capacity(v___x_2174_);
v___x_2176_ = lean_array_push(v___x_2175_, v___x_2170_);
v___x_2177_ = lean_array_push(v___x_2176_, v_a_2157_);
lean_inc_ref(v_currentRetType_2132_);
v___x_2178_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_2153_, v_a_2173_, v_currentRetType_2132_, v___x_2177_, v_a_2165_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2180_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5));
v___x_2181_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2180_, v_a_2139_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2181_, 1);
lean_inc(v_origAllocId_2136_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set_tag(v___x_2167_, 15);
lean_ctor_set(v___x_2167_, 0, v_origAllocId_2136_);
v___x_2184_ = v___x_2167_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_origAllocId_2136_);
v___x_2184_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2153_, v_a_2182_, v___x_2154_, v___x_2184_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v_fvarId_2187_; lean_object* v_fvarId_2188_; lean_object* v___x_2189_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v_fvarId_2187_ = lean_ctor_get(v_a_2179_, 0);
v_fvarId_2188_ = lean_ctor_get(v_a_2186_, 0);
lean_inc(v_fvarId_2188_);
lean_inc(v_fvarId_2187_);
lean_inc(v_origAllocId_2136_);
v___x_2189_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_2136_, v_snd_2146_, v_fvarId_2187_, v_fvarId_2188_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2191_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
lean_inc(v_fvarId_2188_);
lean_inc(v_fvarId_2187_);
v___x_2191_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_2136_, v_snd_2146_, v_fvarId_2187_, v_fvarId_2188_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_snd_2146_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2193_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2191_, 1);
lean_inc(v_fvarId_2188_);
v___x_2193_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_fvarId_2188_, v___x_2154_, v_currentRetType_2132_, v_a_2190_, v_a_2192_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 1);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v_a_2194_);
lean_ctor_set(v___x_2148_, 0, v_a_2186_);
v___x_2196_ = v___x_2148_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2186_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_a_2194_);
v___x_2196_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2153_, v_decl_2134_, v_a_2139_);
lean_dec_ref(v_decl_2134_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2206_; 
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v___x_2197_, 0);
lean_dec(v_unused_2207_);
v___x_2199_ = v___x_2197_;
v_isShared_2200_ = v_isSharedCheck_2206_;
goto v_resetjp_2198_;
}
else
{
lean_dec(v___x_2197_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2206_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_a_2179_);
lean_ctor_set(v___x_2201_, 1, v___x_2196_);
v___x_2202_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_2145_, v___x_2201_);
lean_dec(v_fst_2145_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2202_);
v___x_2204_ = v___x_2199_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v___x_2196_);
lean_dec(v_a_2179_);
lean_dec(v_fst_2145_);
v_a_2208_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2197_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2197_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
else
{
lean_dec(v_a_2186_);
lean_dec(v_a_2179_);
lean_del_object(v___x_2148_);
lean_dec(v_fst_2145_);
lean_dec_ref(v_decl_2134_);
return v___x_2193_;
}
}
else
{
lean_dec(v_a_2190_);
lean_dec(v_a_2186_);
lean_dec(v_a_2179_);
lean_del_object(v___x_2148_);
lean_dec(v_fst_2145_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
return v___x_2191_;
}
}
else
{
lean_dec(v_a_2186_);
lean_dec(v_a_2179_);
lean_del_object(v___x_2148_);
lean_dec(v_snd_2146_);
lean_dec(v_fst_2145_);
lean_dec(v_origAllocId_2136_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
return v___x_2189_;
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_a_2179_);
lean_del_object(v___x_2148_);
lean_dec(v_snd_2146_);
lean_dec(v_fst_2145_);
lean_dec(v_origAllocId_2136_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
v_a_2217_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2185_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2185_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_a_2179_);
lean_del_object(v___x_2167_);
lean_del_object(v___x_2148_);
lean_dec(v_snd_2146_);
lean_dec(v_fst_2145_);
lean_dec(v_origAllocId_2136_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
v_a_2226_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2181_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2181_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_del_object(v___x_2167_);
lean_del_object(v___x_2148_);
lean_dec(v_snd_2146_);
lean_dec(v_fst_2145_);
lean_dec(v_origAllocId_2136_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
v_a_2234_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2178_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2178_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec_ref_known(v___x_2170_, 3);
lean_del_object(v___x_2167_);
lean_dec(v_a_2165_);
lean_dec(v_a_2157_);
lean_del_object(v___x_2148_);
lean_dec(v_snd_2146_);
lean_dec(v_fst_2145_);
lean_dec(v_origAllocId_2136_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
v_a_2242_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2172_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2172_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
}
else
{
lean_dec(v_a_2157_);
lean_del_object(v___x_2148_);
lean_dec(v_snd_2146_);
lean_dec(v_fst_2145_);
lean_dec(v_origAllocId_2136_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
return v___x_2164_;
}
}
else
{
lean_dec(v_a_2157_);
lean_del_object(v___x_2148_);
lean_dec(v_snd_2146_);
lean_dec(v_fst_2145_);
lean_dec(v_origAllocId_2136_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
return v___x_2161_;
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_del_object(v___x_2148_);
lean_dec(v_snd_2146_);
lean_dec(v_fst_2145_);
lean_dec_ref(v_k_2137_);
lean_dec(v_origAllocId_2136_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
v_a_2251_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2156_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2156_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_del_object(v___x_2148_);
lean_dec(v_snd_2146_);
lean_dec(v_fst_2145_);
lean_dec_ref(v_k_2137_);
lean_dec(v_origAllocId_2136_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
v_a_2259_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2151_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2151_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v_k_2137_);
lean_dec(v_origAllocId_2136_);
lean_dec_ref(v_decl_2134_);
lean_dec_ref(v_currentRetType_2132_);
v_a_2268_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2143_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2143_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand_0interp(lean_interpreter_value* stack)
{
lean_object* v_currentRetType_2132_ = stack[0].m_obj;
lean_object* v_ds_2133_ = stack[1].m_obj;
lean_object* v_decl_2134_ = stack[2].m_obj;
lean_object* v_nFields_2135_ = stack[3].m_obj;
lean_object* v_origAllocId_2136_ = stack[4].m_obj;
lean_object* v_k_2137_ = stack[5].m_obj;
lean_object* v_a_2138_ = stack[6].m_obj;
lean_object* v_a_2139_ = stack[7].m_obj;
lean_object* v_a_2140_ = stack[8].m_obj;
lean_object* v_a_2141_ = stack[9].m_obj;
lean_object* v_res_2276_;
v_res_2276_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2132_, v_ds_2133_, v_decl_2134_, v_nFields_2135_, v_origAllocId_2136_, v_k_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
stack->m_obj
 = v_res_2276_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object* v_resultType_2277_, lean_object* v_x_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(v_resultType_2277_, v_x_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
return v_res_2284_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object* v_resultType_2285_, lean_object* v_i_2286_, lean_object* v_as_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = lean_array_get_size(v_as_2287_);
v___x_2294_ = lean_nat_dec_lt(v_i_2286_, v___x_2293_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; 
lean_dec(v_i_2286_);
lean_dec_ref(v_resultType_2285_);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v_as_2287_);
return v___x_2295_;
}
else
{
lean_object* v___f_2296_; lean_object* v_a_2297_; lean_object* v___x_2298_; 
lean_inc_ref(v_resultType_2285_);
v___f_2296_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2296_, 0, v_resultType_2285_);
v_a_2297_ = lean_array_fget_borrowed(v_as_2287_, v_i_2286_);
lean_inc(v_a_2297_);
v___x_2298_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_2297_, v___f_2296_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; size_t v___x_2300_; size_t v___x_2301_; uint8_t v___x_2302_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref_known(v___x_2298_, 1);
v___x_2300_ = lean_ptr_addr(v_a_2297_);
v___x_2301_ = lean_ptr_addr(v_a_2299_);
v___x_2302_ = lean_usize_dec_eq(v___x_2300_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = lean_unsigned_to_nat(1u);
v___x_2304_ = lean_nat_add(v_i_2286_, v___x_2303_);
v___x_2305_ = lean_array_fset(v_as_2287_, v_i_2286_, v_a_2299_);
lean_dec(v_i_2286_);
v_i_2286_ = v___x_2304_;
v_as_2287_ = v___x_2305_;
goto _start;
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec(v_a_2299_);
v___x_2307_ = lean_unsigned_to_nat(1u);
v___x_2308_ = lean_nat_add(v_i_2286_, v___x_2307_);
lean_dec(v_i_2286_);
v_i_2286_ = v___x_2308_;
goto _start;
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_as_2287_);
lean_dec(v_i_2286_);
lean_dec_ref(v_resultType_2285_);
v_a_2310_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2298_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2298_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_resultType_2285_ = stack[0].m_obj;
lean_object* v_i_2286_ = stack[1].m_obj;
lean_object* v_as_2287_ = stack[2].m_obj;
lean_object* v___y_2288_ = stack[3].m_obj;
lean_object* v___y_2289_ = stack[4].m_obj;
lean_object* v___y_2290_ = stack[5].m_obj;
lean_object* v___y_2291_ = stack[6].m_obj;
lean_object* v_res_2318_;
v_res_2318_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2285_, v_i_2286_, v_as_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
stack->m_obj
 = v_res_2318_;
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object* v_code_2319_, lean_object* v_ds_2320_, lean_object* v_currentRetType_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_code_2328_; lean_object* v_ds_2329_; lean_object* v_k_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; 
switch(lean_obj_tag(v_code_2319_))
{
case 0:
{
lean_object* v_decl_2339_; lean_object* v_value_2340_; 
v_decl_2339_ = lean_ctor_get(v_code_2319_, 0);
v_value_2340_ = lean_ctor_get(v_decl_2339_, 3);
if (lean_obj_tag(v_value_2340_) == 11)
{
lean_object* v_k_2341_; lean_object* v_n_2342_; lean_object* v_var_2343_; lean_object* v___x_2344_; 
lean_inc_ref(v_decl_2339_);
v_k_2341_ = lean_ctor_get(v_code_2319_, 1);
lean_inc_ref(v_k_2341_);
lean_dec_ref_known(v_code_2319_, 2);
v_n_2342_ = lean_ctor_get(v_value_2340_, 0);
lean_inc(v_n_2342_);
v_var_2343_ = lean_ctor_get(v_value_2340_, 1);
lean_inc(v_var_2343_);
v___x_2344_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2321_, v_ds_2320_, v_decl_2339_, v_n_2342_, v_var_2343_, v_k_2341_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
return v___x_2344_;
}
else
{
lean_object* v_k_2345_; 
v_k_2345_ = lean_ctor_get(v_code_2319_, 1);
lean_inc_ref(v_k_2345_);
v_code_2328_ = v_code_2319_;
v_ds_2329_ = v_ds_2320_;
v_k_2330_ = v_k_2345_;
v___y_2331_ = v_a_2322_;
v___y_2332_ = v_a_2323_;
v___y_2333_ = v_a_2324_;
v___y_2334_ = v_a_2325_;
goto v___jp_2327_;
}
}
case 2:
{
lean_object* v_decl_2346_; lean_object* v_k_2347_; lean_object* v_params_2348_; lean_object* v_type_2349_; lean_object* v_value_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v_decl_2346_ = lean_ctor_get(v_code_2319_, 0);
lean_inc_ref(v_decl_2346_);
v_k_2347_ = lean_ctor_get(v_code_2319_, 1);
lean_inc_ref(v_k_2347_);
lean_dec_ref_known(v_code_2319_, 2);
v_params_2348_ = lean_ctor_get(v_decl_2346_, 2);
lean_inc_ref(v_params_2348_);
v_type_2349_ = lean_ctor_get(v_decl_2346_, 3);
lean_inc_ref_n(v_type_2349_, 2);
v_value_2350_ = lean_ctor_get(v_decl_2346_, 4);
v___x_2351_ = 1;
v___x_2352_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_value_2350_);
v___x_2353_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_value_2350_, v___x_2352_, v_type_2349_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2373_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2373_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2373_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; 
v___x_2358_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2351_, v_decl_2346_, v_type_2349_, v_params_2348_, v_a_2354_, v_a_2323_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
if (v_isShared_2357_ == 0)
{
lean_ctor_set_tag(v___x_2356_, 2);
lean_ctor_set(v___x_2356_, 0, v_a_2359_);
v___x_2361_ = v___x_2356_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2359_);
v___x_2361_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_array_push(v_ds_2320_, v___x_2361_);
v_code_2319_ = v_k_2347_;
v_ds_2320_ = v___x_2362_;
goto _start;
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_del_object(v___x_2356_);
lean_dec_ref(v_k_2347_);
lean_dec_ref(v_currentRetType_2321_);
lean_dec_ref(v_ds_2320_);
v_a_2365_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2358_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2358_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_2349_);
lean_dec_ref(v_params_2348_);
lean_dec_ref(v_k_2347_);
lean_dec_ref(v_decl_2346_);
lean_dec_ref(v_currentRetType_2321_);
lean_dec_ref(v_ds_2320_);
return v___x_2353_;
}
}
case 4:
{
lean_object* v_cases_2374_; lean_object* v_typeName_2375_; lean_object* v_resultType_2376_; lean_object* v_discr_2377_; lean_object* v_alts_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v_currentRetType_2321_);
v_cases_2374_ = lean_ctor_get(v_code_2319_, 0);
lean_inc_ref(v_cases_2374_);
v_typeName_2375_ = lean_ctor_get(v_cases_2374_, 0);
v_resultType_2376_ = lean_ctor_get(v_cases_2374_, 1);
v_discr_2377_ = lean_ctor_get(v_cases_2374_, 2);
v_alts_2378_ = lean_ctor_get(v_cases_2374_, 3);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_cases_2374_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2380_ = v_cases_2374_;
v_isShared_2381_ = v_isSharedCheck_2417_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_alts_2378_);
lean_inc(v_discr_2377_);
lean_inc(v_resultType_2376_);
lean_inc(v_typeName_2375_);
lean_dec(v_cases_2374_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2417_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2378_);
lean_inc_ref(v_resultType_2376_);
v___x_2383_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2376_, v___x_2382_, v_alts_2378_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2408_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2408_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2408_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___y_2389_; size_t v___x_2394_; size_t v___x_2395_; uint8_t v___x_2396_; 
v___x_2394_ = lean_ptr_addr(v_alts_2378_);
lean_dec_ref(v_alts_2378_);
v___x_2395_ = lean_ptr_addr(v_a_2384_);
v___x_2396_ = lean_usize_dec_eq(v___x_2394_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2406_; 
v_isSharedCheck_2406_ = !lean_is_exclusive(v_code_2319_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; 
v_unused_2407_ = lean_ctor_get(v_code_2319_, 0);
lean_dec(v_unused_2407_);
v___x_2398_ = v_code_2319_;
v_isShared_2399_ = v_isSharedCheck_2406_;
goto v_resetjp_2397_;
}
else
{
lean_dec(v_code_2319_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2406_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 3, v_a_2384_);
v___x_2401_ = v___x_2380_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_typeName_2375_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_resultType_2376_);
lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_discr_2377_);
lean_ctor_set(v_reuseFailAlloc_2405_, 3, v_a_2384_);
v___x_2401_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2403_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2401_);
v___x_2403_ = v___x_2398_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
v___y_2389_ = v___x_2403_;
goto v___jp_2388_;
}
}
}
}
else
{
lean_dec(v_a_2384_);
lean_del_object(v___x_2380_);
lean_dec(v_discr_2377_);
lean_dec_ref(v_resultType_2376_);
lean_dec(v_typeName_2375_);
v___y_2389_ = v_code_2319_;
goto v___jp_2388_;
}
v___jp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2390_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_ds_2320_, v___y_2389_);
lean_dec_ref(v_ds_2320_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2390_);
v___x_2392_ = v___x_2386_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_del_object(v___x_2380_);
lean_dec_ref(v_alts_2378_);
lean_dec(v_discr_2377_);
lean_dec_ref(v_resultType_2376_);
lean_dec(v_typeName_2375_);
lean_dec_ref_known(v_code_2319_, 1);
lean_dec_ref(v_ds_2320_);
v_a_2409_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2383_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2383_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
case 7:
{
lean_object* v_k_2418_; 
v_k_2418_ = lean_ctor_get(v_code_2319_, 3);
lean_inc_ref(v_k_2418_);
v_code_2328_ = v_code_2319_;
v_ds_2329_ = v_ds_2320_;
v_k_2330_ = v_k_2418_;
v___y_2331_ = v_a_2322_;
v___y_2332_ = v_a_2323_;
v___y_2333_ = v_a_2324_;
v___y_2334_ = v_a_2325_;
goto v___jp_2327_;
}
case 8:
{
lean_object* v_k_2419_; 
v_k_2419_ = lean_ctor_get(v_code_2319_, 3);
lean_inc_ref(v_k_2419_);
v_code_2328_ = v_code_2319_;
v_ds_2329_ = v_ds_2320_;
v_k_2330_ = v_k_2419_;
v___y_2331_ = v_a_2322_;
v___y_2332_ = v_a_2323_;
v___y_2333_ = v_a_2324_;
v___y_2334_ = v_a_2325_;
goto v___jp_2327_;
}
case 9:
{
lean_object* v_k_2420_; 
v_k_2420_ = lean_ctor_get(v_code_2319_, 5);
lean_inc_ref(v_k_2420_);
v_code_2328_ = v_code_2319_;
v_ds_2329_ = v_ds_2320_;
v_k_2330_ = v_k_2420_;
v___y_2331_ = v_a_2322_;
v___y_2332_ = v_a_2323_;
v___y_2333_ = v_a_2324_;
v___y_2334_ = v_a_2325_;
goto v___jp_2327_;
}
case 10:
{
lean_object* v_k_2421_; 
v_k_2421_ = lean_ctor_get(v_code_2319_, 2);
lean_inc_ref(v_k_2421_);
v_code_2328_ = v_code_2319_;
v_ds_2329_ = v_ds_2320_;
v_k_2330_ = v_k_2421_;
v___y_2331_ = v_a_2322_;
v___y_2332_ = v_a_2323_;
v___y_2333_ = v_a_2324_;
v___y_2334_ = v_a_2325_;
goto v___jp_2327_;
}
case 11:
{
lean_object* v_k_2422_; 
v_k_2422_ = lean_ctor_get(v_code_2319_, 2);
lean_inc_ref(v_k_2422_);
v_code_2328_ = v_code_2319_;
v_ds_2329_ = v_ds_2320_;
v_k_2330_ = v_k_2422_;
v___y_2331_ = v_a_2322_;
v___y_2332_ = v_a_2323_;
v___y_2333_ = v_a_2324_;
v___y_2334_ = v_a_2325_;
goto v___jp_2327_;
}
case 12:
{
lean_object* v_k_2423_; 
v_k_2423_ = lean_ctor_get(v_code_2319_, 3);
lean_inc_ref(v_k_2423_);
v_code_2328_ = v_code_2319_;
v_ds_2329_ = v_ds_2320_;
v_k_2330_ = v_k_2423_;
v___y_2331_ = v_a_2322_;
v___y_2332_ = v_a_2323_;
v___y_2333_ = v_a_2324_;
v___y_2334_ = v_a_2325_;
goto v___jp_2327_;
}
case 13:
{
lean_object* v_k_2424_; 
v_k_2424_ = lean_ctor_get(v_code_2319_, 1);
lean_inc_ref(v_k_2424_);
v_code_2328_ = v_code_2319_;
v_ds_2329_ = v_ds_2320_;
v_k_2330_ = v_k_2424_;
v___y_2331_ = v_a_2322_;
v___y_2332_ = v_a_2323_;
v___y_2333_ = v_a_2324_;
v___y_2334_ = v_a_2325_;
goto v___jp_2327_;
}
default: 
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec_ref(v_currentRetType_2321_);
v___x_2425_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_ds_2320_, v_code_2319_);
lean_dec_ref(v_ds_2320_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
}
v___jp_2327_:
{
uint8_t v___x_2335_; lean_object* v_d_2336_; lean_object* v___x_2337_; 
v___x_2335_ = 1;
v_d_2336_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_2335_, v_code_2328_);
lean_dec_ref(v_code_2328_);
v___x_2337_ = lean_array_push(v_ds_2329_, v_d_2336_);
v_code_2319_ = v_k_2330_;
v_ds_2320_ = v___x_2337_;
v_a_2322_ = v___y_2331_;
v_a_2323_ = v___y_2332_;
v_a_2324_ = v___y_2333_;
v_a_2325_ = v___y_2334_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_2319_ = stack[0].m_obj;
lean_object* v_ds_2320_ = stack[1].m_obj;
lean_object* v_currentRetType_2321_ = stack[2].m_obj;
lean_object* v_a_2322_ = stack[3].m_obj;
lean_object* v_a_2323_ = stack[4].m_obj;
lean_object* v_a_2324_ = stack[5].m_obj;
lean_object* v_a_2325_ = stack[6].m_obj;
lean_object* v_res_2427_;
v_res_2427_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_code_2319_, v_ds_2320_, v_currentRetType_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
stack->m_obj
 = v_res_2427_;
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object* v_resultType_2428_, lean_object* v_x_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2436_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2429_, v___x_2435_, v_resultType_2428_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
return v___x_2436_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_resultType_2428_ = stack[0].m_obj;
lean_object* v_x_2429_ = stack[1].m_obj;
lean_object* v___y_2430_ = stack[2].m_obj;
lean_object* v___y_2431_ = stack[3].m_obj;
lean_object* v___y_2432_ = stack[4].m_obj;
lean_object* v___y_2433_ = stack[5].m_obj;
lean_object* v_res_2437_;
v_res_2437_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(v_resultType_2428_, v_x_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
stack->m_obj
 = v_res_2437_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object* v_resultType_2438_, lean_object* v_i_2439_, lean_object* v_as_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2438_, v_i_2439_, v_as_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object* v_code_2447_, lean_object* v_ds_2448_, lean_object* v_currentRetType_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_code_2447_, v_ds_2448_, v_currentRetType_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object* v_currentRetType_2456_, lean_object* v_ds_2457_, lean_object* v_decl_2458_, lean_object* v_nFields_2459_, lean_object* v_origAllocId_2460_, lean_object* v_k_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2456_, v_ds_2457_, v_decl_2458_, v_nFields_2459_, v_origAllocId_2460_, v_k_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
return v_res_2467_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object* v_f_2468_, lean_object* v_v_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
if (lean_obj_tag(v_v_2469_) == 0)
{
lean_object* v_code_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2499_; 
v_code_2475_ = lean_ctor_get(v_v_2469_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_v_2469_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2477_ = v_v_2469_;
v_isShared_2478_ = v_isSharedCheck_2499_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_code_2475_);
lean_dec(v_v_2469_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2499_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; 
lean_inc(v___y_2473_);
lean_inc_ref(v___y_2472_);
lean_inc(v___y_2471_);
lean_inc_ref(v___y_2470_);
v___x_2479_ = lean_apply_6(v_f_2468_, v_code_2475_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, lean_box(0));
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2490_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2490_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2490_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v_a_2480_);
v___x_2485_ = v___x_2477_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2485_);
v___x_2487_ = v___x_2482_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_del_object(v___x_2477_);
v_a_2491_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2479_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2479_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
else
{
lean_object* v___x_2500_; 
lean_dec_ref(v_f_2468_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_v_2469_);
return v___x_2500_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2468_ = stack[0].m_obj;
lean_object* v_v_2469_ = stack[1].m_obj;
lean_object* v___y_2470_ = stack[2].m_obj;
lean_object* v___y_2471_ = stack[3].m_obj;
lean_object* v___y_2472_ = stack[4].m_obj;
lean_object* v___y_2473_ = stack[5].m_obj;
lean_object* v_res_2501_;
v_res_2501_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2468_, v_v_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
stack->m_obj
 = v_res_2501_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object* v_f_2502_, lean_object* v_v_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2502_, v_v_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2509_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t v_pu_2510_, lean_object* v_f_2511_, lean_object* v_v_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2511_, v_v_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2518_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2510_ = stack[0].m_num;
lean_object* v_f_2511_ = stack[1].m_obj;
lean_object* v_v_2512_ = stack[2].m_obj;
lean_object* v___y_2513_ = stack[3].m_obj;
lean_object* v___y_2514_ = stack[4].m_obj;
lean_object* v___y_2515_ = stack[5].m_obj;
lean_object* v___y_2516_ = stack[6].m_obj;
lean_object* v_res_2519_;
v_res_2519_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(v_pu_2510_, v_f_2511_, v_v_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
stack->m_obj
 = v_res_2519_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object* v_pu_2520_, lean_object* v_f_2521_, lean_object* v_v_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
uint8_t v_pu_boxed_2528_; lean_object* v_res_2529_; 
v_pu_boxed_2528_ = lean_unbox(v_pu_2520_);
v_res_2529_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(v_pu_boxed_2528_, v_f_2521_, v_v_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
return v_res_2529_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object* v_decl_2530_, lean_object* v_x_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_toSignature_2537_; lean_object* v_type_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v_toSignature_2537_ = lean_ctor_get(v_decl_2530_, 0);
lean_inc_ref(v_toSignature_2537_);
lean_dec_ref(v_decl_2530_);
v_type_2538_ = lean_ctor_get(v_toSignature_2537_, 2);
lean_inc_ref(v_type_2538_);
lean_dec_ref(v_toSignature_2537_);
v___x_2539_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2540_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2531_, v___x_2539_, v_type_2538_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
return v___x_2540_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2530_ = stack[0].m_obj;
lean_object* v_x_2531_ = stack[1].m_obj;
lean_object* v___y_2532_ = stack[2].m_obj;
lean_object* v___y_2533_ = stack[3].m_obj;
lean_object* v___y_2534_ = stack[4].m_obj;
lean_object* v___y_2535_ = stack[5].m_obj;
lean_object* v_res_2541_;
v_res_2541_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(v_decl_2530_, v_x_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
stack->m_obj
 = v_res_2541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object* v_decl_2542_, lean_object* v_x_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(v_decl_2542_, v_x_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2549_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object* v_decl_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___f_2556_; lean_object* v___x_2557_; 
lean_inc_ref(v_decl_2550_);
v___f_2556_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2556_, 0, v_decl_2550_);
v___x_2557_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2551_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2594_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2594_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2594_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
uint8_t v_resetReuse_2562_; 
v_resetReuse_2562_ = lean_ctor_get_uint8(v_a_2558_, sizeof(void*)*4 + 2);
lean_dec(v_a_2558_);
if (v_resetReuse_2562_ == 0)
{
lean_object* v___x_2564_; 
lean_dec_ref(v___f_2556_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v_decl_2550_);
v___x_2564_ = v___x_2560_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_decl_2550_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
else
{
lean_object* v_toSignature_2566_; lean_object* v_value_2567_; uint8_t v_recursive_2568_; lean_object* v_inlineAttr_x3f_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2593_; 
lean_del_object(v___x_2560_);
v_toSignature_2566_ = lean_ctor_get(v_decl_2550_, 0);
v_value_2567_ = lean_ctor_get(v_decl_2550_, 1);
v_recursive_2568_ = lean_ctor_get_uint8(v_decl_2550_, sizeof(void*)*3);
v_inlineAttr_x3f_2569_ = lean_ctor_get(v_decl_2550_, 2);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_decl_2550_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2571_ = v_decl_2550_;
v_isShared_2572_ = v_isSharedCheck_2593_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_inlineAttr_x3f_2569_);
lean_inc(v_value_2567_);
lean_inc(v_toSignature_2566_);
lean_dec(v_decl_2550_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2593_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v___f_2556_, v_value_2567_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2584_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2584_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2584_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v_a_2574_);
v___x_2579_ = v___x_2571_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_toSignature_2566_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_a_2574_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_inlineAttr_x3f_2569_);
lean_ctor_set_uint8(v_reuseFailAlloc_2583_, sizeof(void*)*3, v_recursive_2568_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2579_);
v___x_2581_ = v___x_2576_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_del_object(v___x_2571_);
lean_dec(v_inlineAttr_x3f_2569_);
lean_dec_ref(v_toSignature_2566_);
v_a_2585_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2573_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2573_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v___f_2556_);
lean_dec_ref(v_decl_2550_);
v_a_2595_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2557_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2557_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2550_ = stack[0].m_obj;
lean_object* v_a_2551_ = stack[1].m_obj;
lean_object* v_a_2552_ = stack[2].m_obj;
lean_object* v_a_2553_ = stack[3].m_obj;
lean_object* v_a_2554_ = stack[4].m_obj;
lean_object* v_res_2603_;
v_res_2603_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(v_decl_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
stack->m_obj
 = v_res_2603_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object* v_decl_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(v_decl_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
return v_res_2610_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__2));
v___x_2617_ = 2;
v___x_2618_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__1));
v___x_2619_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_2618_, v___x_2617_, v___x_2616_, v___x_2615_);
return v___x_2619_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse(void){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = lean_obj_once(&l_Lean_Compiler_LCNF_expandResetReuse___closed__3, &l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3);
return v___x_2620_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = lean_unsigned_to_nat(2743268278u);
v___x_2677_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2678_ = l_Lean_Name_num___override(v___x_2677_, v___x_2676_);
return v___x_2678_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2681_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2682_ = l_Lean_Name_str___override(v___x_2681_, v___x_2680_);
return v___x_2682_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2685_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2686_ = l_Lean_Name_str___override(v___x_2685_, v___x_2684_);
return v___x_2686_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = lean_unsigned_to_nat(2u);
v___x_2688_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2689_ = l_Lean_Name_num___override(v___x_2688_, v___x_2687_);
return v___x_2689_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2691_; uint8_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2691_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2692_ = 1;
v___x_2693_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2694_ = l_Lean_registerTraceClass(v___x_2691_, v___x_2692_, v___x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2695_;
v_res_2695_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2695_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
return v_res_2697_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_expandResetReuse = _init_l_Lean_Compiler_LCNF_expandResetReuse();
lean_mark_persistent(l_Lean_Compiler_LCNF_expandResetReuse);
res = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
}
#ifdef __cplusplus
}
#endif
