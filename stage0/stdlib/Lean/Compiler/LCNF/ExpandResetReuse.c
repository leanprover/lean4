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
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
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
v___x_1_ = l_instMonadEIO(lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Array_instInhabited(lean_box(0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(lean_object* v_msg_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___boxed(lean_object* v_msg_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v_msg_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(lean_object* v_fst_58_, lean_object* v_snd_59_, lean_object* v_fst_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_fst_58_);
lean_ctor_set(v___x_67_, 1, v_snd_59_);
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v_fst_60_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0___boxed(lean_object* v_fst_71_, lean_object* v_snd_72_, lean_object* v_fst_73_, lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_71_, v_snd_72_, v_fst_73_, v_x_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec_ref(v_x_74_);
return v_res_80_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0(void){
_start:
{
uint8_t v___x_81_; lean_object* v___x_82_; 
v___x_81_ = 1;
v___x_82_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_86_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3));
v___x_87_ = lean_unsigned_to_nat(6u);
v___x_88_ = lean_unsigned_to_nat(87u);
v___x_89_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2));
v___x_90_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_91_ = l_mkPanicMessageWithDecl(v___x_90_, v___x_89_, v___x_88_, v___x_87_, v___x_86_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(lean_object* v_targetId_92_, lean_object* v_a_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_107_; lean_object* v_snd_127_; lean_object* v_fst_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_270_; 
v_snd_127_ = lean_ctor_get(v_a_93_, 1);
v_fst_128_ = lean_ctor_get(v_a_93_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_a_93_);
if (v_isSharedCheck_270_ == 0)
{
v___x_130_ = v_a_93_;
v_isShared_131_ = v_isSharedCheck_270_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_snd_127_);
lean_inc(v_fst_128_);
lean_dec(v_a_93_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_270_;
goto v_resetjp_129_;
}
v___jp_99_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___y_102_);
lean_ctor_set(v___x_103_, 1, v___y_101_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___y_100_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v_a_93_ = v___x_104_;
goto _start;
}
v___jp_106_:
{
if (lean_obj_tag(v___y_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_118_; 
v_a_108_ = lean_ctor_get(v___y_107_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___y_107_);
if (v_isSharedCheck_118_ == 0)
{
v___x_110_ = v___y_107_;
v_isShared_111_ = v_isSharedCheck_118_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___y_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_118_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
if (lean_obj_tag(v_a_108_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; 
v_a_112_ = lean_ctor_get(v_a_108_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v_a_108_, 1);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v_a_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
else
{
lean_object* v_a_116_; 
lean_del_object(v___x_110_);
v_a_116_ = lean_ctor_get(v_a_108_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v_a_108_, 1);
v_a_93_ = v_a_116_;
goto _start;
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
v_a_119_ = lean_ctor_get(v___y_107_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___y_107_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___y_107_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___y_107_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
v_resetjp_129_:
{
lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_269_; 
v_fst_132_ = lean_ctor_get(v_snd_127_, 0);
v_snd_133_ = lean_ctor_get(v_snd_127_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_snd_127_);
if (v_isSharedCheck_269_ == 0)
{
v___x_135_ = v_snd_127_;
v_isShared_136_ = v_isSharedCheck_269_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_snd_133_);
lean_inc(v_fst_132_);
lean_dec(v_snd_127_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_269_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = lean_array_get_size(v_fst_128_);
v___x_139_ = lean_nat_dec_le(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_141_; 
if (v_isShared_136_ == 0)
{
v___x_141_ = v___x_135_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_fst_132_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_snd_133_);
v___x_141_ = v_reuseFailAlloc_146_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_143_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_141_);
v___x_143_ = v___x_130_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_fst_128_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_145_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_sub(v___x_138_, v___x_148_);
v___x_150_ = lean_array_get(v___x_147_, v_fst_128_, v___x_149_);
lean_dec(v___x_149_);
switch(lean_obj_tag(v___x_150_))
{
case 0:
{
lean_object* v_decl_151_; lean_object* v_value_152_; 
v_decl_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc_ref(v_decl_151_);
v_value_152_ = lean_ctor_get(v_decl_151_, 3);
lean_inc(v_value_152_);
switch(lean_obj_tag(v_value_152_))
{
case 8:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
lean_dec_ref_known(v_value_152_, 3);
lean_dec_ref(v_decl_151_);
v___x_153_ = lean_array_pop(v_fst_128_);
v___x_154_ = lean_array_push(v_fst_132_, v___x_150_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_154_);
v___x_156_ = v___x_135_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_snd_133_);
v___x_156_ = v_reuseFailAlloc_161_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_158_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_156_);
lean_ctor_set(v___x_130_, 0, v___x_153_);
v___x_158_ = v___x_130_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
v_a_93_ = v___x_158_;
goto _start;
}
}
}
case 7:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
lean_dec_ref_known(v_value_152_, 2);
lean_dec_ref(v_decl_151_);
v___x_162_ = lean_array_pop(v_fst_128_);
v___x_163_ = lean_array_push(v_fst_132_, v___x_150_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_163_);
v___x_165_ = v___x_135_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_snd_133_);
v___x_165_ = v_reuseFailAlloc_170_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_165_);
lean_ctor_set(v___x_130_, 0, v___x_162_);
v___x_167_ = v___x_130_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_169_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
v_a_93_ = v___x_167_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_189_; 
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_190_);
v___x_172_ = v___x_150_;
v_isShared_173_ = v_isSharedCheck_189_;
goto v_resetjp_171_;
}
else
{
lean_dec(v___x_150_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_189_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v_fvarId_174_; lean_object* v_binderName_175_; lean_object* v_type_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_187_; 
v_fvarId_174_ = lean_ctor_get(v_decl_151_, 0);
v_binderName_175_ = lean_ctor_get(v_decl_151_, 1);
v_type_176_ = lean_ctor_get(v_decl_151_, 2);
v_isSharedCheck_187_ = !lean_is_exclusive(v_decl_151_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_decl_151_, 3);
lean_dec(v_unused_188_);
v___x_178_ = v_decl_151_;
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_type_176_);
lean_inc(v_binderName_175_);
lean_inc(v_fvarId_174_);
lean_dec(v_decl_151_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_fvarId_174_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_binderName_175_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_type_176_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_value_152_);
v___x_181_ = v_reuseFailAlloc_186_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_181_);
v___x_183_ = v___x_172_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_185_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_183_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec_ref(v___x_183_);
v___y_107_ = v___x_184_;
goto v___jp_106_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_191_; lean_object* v_n_192_; uint8_t v_check_193_; uint8_t v_persistent_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_fvarId_191_ = lean_ctor_get(v___x_150_, 0);
v_n_192_ = lean_ctor_get(v___x_150_, 1);
v_check_193_ = lean_ctor_get_uint8(v___x_150_, sizeof(void*)*2);
v_persistent_194_ = lean_ctor_get_uint8(v___x_150_, sizeof(void*)*2 + 1);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_nat_dec_lt(v___x_195_, v_n_192_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec_ref_known(v___x_150_, 2);
lean_del_object(v___x_135_);
lean_dec(v_snd_133_);
lean_dec(v_fst_132_);
lean_del_object(v___x_130_);
lean_dec(v_fst_128_);
v___x_197_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4);
v___x_198_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v___x_197_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
v___y_107_ = v___x_198_;
goto v___jp_106_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_nat_sub(v___x_138_, v___x_137_);
v___x_200_ = lean_array_get(v___x_147_, v_fst_128_, v___x_199_);
lean_dec(v___x_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_decl_201_; lean_object* v_value_202_; 
v_decl_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc_ref(v_decl_201_);
v_value_202_ = lean_ctor_get(v_decl_201_, 3);
lean_inc(v_value_202_);
if (lean_obj_tag(v_value_202_) == 6)
{
lean_object* v_fvarId_203_; lean_object* v_i_204_; lean_object* v_var_205_; lean_object* v___x_206_; uint8_t v___y_208_; uint8_t v___x_245_; 
v_fvarId_203_ = lean_ctor_get(v_decl_201_, 0);
lean_inc(v_fvarId_203_);
lean_dec_ref(v_decl_201_);
v_i_204_ = lean_ctor_get(v_value_202_, 0);
lean_inc(v_i_204_);
v_var_205_ = lean_ctor_get(v_value_202_, 1);
lean_inc(v_var_205_);
lean_dec_ref_known(v_value_202_, 2);
v___x_206_ = lean_box(0);
v___x_245_ = l_Lean_instBEqFVarId_beq(v_fvarId_203_, v_fvarId_191_);
lean_dec(v_fvarId_203_);
if (v___x_245_ == 0)
{
lean_dec(v_var_205_);
v___y_208_ = v___x_245_;
goto v___jp_207_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = l_Lean_instBEqFVarId_beq(v_targetId_92_, v_var_205_);
lean_dec(v_var_205_);
v___y_208_ = v___x_246_;
goto v___jp_207_;
}
v___jp_207_:
{
if (v___y_208_ == 0)
{
lean_object* v___x_210_; 
lean_dec(v_i_204_);
lean_dec_ref_known(v___x_200_, 1);
lean_dec_ref_known(v___x_150_, 2);
if (v_isShared_136_ == 0)
{
v___x_210_ = v___x_135_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_fst_132_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_snd_133_);
v___x_210_ = v_reuseFailAlloc_215_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_210_);
v___x_212_ = v___x_130_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_fst_128_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_214_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; 
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_array_get_borrowed(v___x_206_, v_snd_133_, v_i_204_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_231_; 
lean_inc(v_n_192_);
lean_inc(v_fvarId_191_);
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_232_ = lean_ctor_get(v___x_150_, 1);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_233_);
v___x_218_ = v___x_150_;
v_isShared_219_ = v_isSharedCheck_231_;
goto v_resetjp_217_;
}
else
{
lean_dec(v___x_150_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_231_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_220_ = lean_array_pop(v_fst_128_);
v___x_221_ = lean_array_pop(v___x_220_);
lean_inc(v_fvarId_191_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v_fvarId_191_);
v___x_223_ = lean_array_set(v_snd_133_, v_i_204_, v___x_222_);
lean_dec(v_i_204_);
v___x_224_ = lean_array_push(v_fst_132_, v___x_200_);
v___x_225_ = lean_nat_dec_eq(v_n_192_, v___x_148_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_nat_sub(v_n_192_, v___x_148_);
lean_dec(v_n_192_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v___x_226_);
v___x_228_ = v___x_218_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_fvarId_191_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_226_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*2, v_check_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*2 + 1, v_persistent_194_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_array_push(v___x_224_, v___x_228_);
v___y_100_ = v___x_221_;
v___y_101_ = v___x_223_;
v___y_102_ = v___x_229_;
goto v___jp_99_;
}
}
else
{
lean_del_object(v___x_218_);
lean_dec(v_n_192_);
lean_dec(v_fvarId_191_);
v___y_100_ = v___x_221_;
v___y_101_ = v___x_223_;
v___y_102_ = v___x_224_;
goto v___jp_99_;
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
lean_dec(v_i_204_);
v___x_234_ = lean_array_push(v_fst_132_, v___x_150_);
v___x_235_ = lean_array_push(v___x_234_, v___x_200_);
v___x_236_ = lean_array_pop(v_fst_128_);
v___x_237_ = lean_array_pop(v___x_236_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_235_);
v___x_239_ = v___x_135_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_snd_133_);
v___x_239_ = v_reuseFailAlloc_244_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_239_);
lean_ctor_set(v___x_130_, 0, v___x_237_);
v___x_241_ = v___x_130_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
v_a_93_ = v___x_241_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_265_; 
lean_dec_ref_known(v___x_150_, 2);
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v___x_200_, 0);
lean_dec(v_unused_266_);
v___x_248_ = v___x_200_;
v_isShared_249_ = v_isSharedCheck_265_;
goto v_resetjp_247_;
}
else
{
lean_dec(v___x_200_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_265_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v_fvarId_250_; lean_object* v_binderName_251_; lean_object* v_type_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_263_; 
v_fvarId_250_ = lean_ctor_get(v_decl_201_, 0);
v_binderName_251_ = lean_ctor_get(v_decl_201_, 1);
v_type_252_ = lean_ctor_get(v_decl_201_, 2);
v_isSharedCheck_263_ = !lean_is_exclusive(v_decl_201_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; 
v_unused_264_ = lean_ctor_get(v_decl_201_, 3);
lean_dec(v_unused_264_);
v___x_254_ = v_decl_201_;
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_type_252_);
lean_inc(v_binderName_251_);
lean_inc(v_fvarId_250_);
lean_dec(v_decl_201_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_fvarId_250_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_binderName_251_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_type_252_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_value_202_);
v___x_257_ = v_reuseFailAlloc_262_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_257_);
v___x_259_ = v___x_248_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_261_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_259_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec_ref(v___x_259_);
v___y_107_ = v___x_260_;
goto v___jp_106_;
}
}
}
}
}
}
else
{
lean_object* v___x_267_; 
lean_dec_ref_known(v___x_150_, 2);
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v___x_267_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_200_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___x_200_);
v___y_107_ = v___x_267_;
goto v___jp_106_;
}
}
}
default: 
{
lean_object* v___x_268_; 
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v___x_268_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_150_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___x_150_);
v___y_107_ = v___x_268_;
goto v___jp_106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(lean_object* v_targetId_271_, lean_object* v_a_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_271_, v_a_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v_targetId_271_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object* v_nFields_281_, lean_object* v_targetId_282_, lean_object* v_ds_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_keep_289_; lean_object* v___x_290_; lean_object* v_mask_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_keep_289_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_290_ = lean_box(0);
v_mask_291_ = lean_mk_array(v_nFields_281_, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_keep_289_);
lean_ctor_set(v___x_292_, 1, v_mask_291_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_ds_283_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_282_, v___x_293_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_315_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_315_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_315_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_315_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v_snd_299_; lean_object* v_fst_300_; lean_object* v_fst_301_; lean_object* v_snd_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_314_; 
v_snd_299_ = lean_ctor_get(v_a_295_, 1);
lean_inc(v_snd_299_);
v_fst_300_ = lean_ctor_get(v_a_295_, 0);
lean_inc(v_fst_300_);
lean_dec(v_a_295_);
v_fst_301_ = lean_ctor_get(v_snd_299_, 0);
v_snd_302_ = lean_ctor_get(v_snd_299_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_snd_299_);
if (v_isSharedCheck_314_ == 0)
{
v___x_304_ = v_snd_299_;
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_snd_302_);
lean_inc(v_fst_301_);
lean_dec(v_snd_299_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_306_ = l_Array_reverse___redArg(v_fst_301_);
v___x_307_ = l_Array_append___redArg(v_fst_300_, v___x_306_);
lean_dec_ref(v___x_306_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_307_);
v___x_309_ = v___x_304_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_snd_302_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_309_);
v___x_311_ = v___x_297_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_294_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_294_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object* v_nFields_324_, lean_object* v_targetId_325_, lean_object* v_ds_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_324_, v_targetId_325_, v_ds_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_targetId_325_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object* v_targetId_333_, lean_object* v_inst_334_, lean_object* v_a_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_333_, v_a_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object* v_targetId_342_, lean_object* v_inst_343_, lean_object* v_a_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(v_targetId_342_, v_inst_343_, v_a_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v_targetId_342_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object* v_discr_367_, lean_object* v_discrType_368_, lean_object* v_resultType_369_, lean_object* v_t_370_, lean_object* v_e_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_373_ = l_Lean_Expr_getAppFn(v_discrType_368_);
v___x_374_ = l_Lean_Expr_constName_x21(v___x_373_);
lean_dec_ref(v___x_373_);
v___x_375_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3));
v___x_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_e_371_);
v___x_377_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6));
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v_t_370_);
v___x_379_ = lean_unsigned_to_nat(2u);
v___x_380_ = lean_mk_empty_array_with_capacity(v___x_379_);
v___x_381_ = lean_array_push(v___x_380_, v___x_376_);
v___x_382_ = lean_array_push(v___x_381_, v___x_378_);
v___x_383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_383_, 0, v___x_374_);
lean_ctor_set(v___x_383_, 1, v_resultType_369_);
lean_ctor_set(v___x_383_, 2, v_discr_367_);
lean_ctor_set(v___x_383_, 3, v___x_382_);
v___x_384_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object* v_discr_386_, lean_object* v_discrType_387_, lean_object* v_resultType_388_, lean_object* v_t_389_, lean_object* v_e_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_386_, v_discrType_387_, v_resultType_388_, v_t_389_, v_e_390_);
lean_dec_ref(v_discrType_387_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object* v_discr_393_, lean_object* v_discrType_394_, lean_object* v_resultType_395_, lean_object* v_t_396_, lean_object* v_e_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_393_, v_discrType_394_, v_resultType_395_, v_t_396_, v_e_397_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object* v_discr_404_, lean_object* v_discrType_405_, lean_object* v_resultType_406_, lean_object* v_t_407_, lean_object* v_e_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(v_discr_404_, v_discrType_405_, v_resultType_406_, v_t_407_, v_e_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec_ref(v_discrType_405_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object* v_msg_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_417_ = lean_panic_fn_borrowed(v___x_416_, v_msg_415_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_421_ = lean_unsigned_to_nat(11u);
v___x_422_ = lean_unsigned_to_nat(138u);
v___x_423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0));
v___x_424_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_425_ = l_mkPanicMessageWithDecl(v___x_424_, v___x_423_, v___x_422_, v___x_421_, v___x_420_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object* v_targetId_426_, size_t v_sz_427_, size_t v_i_428_, lean_object* v_bs_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_428_, v_sz_427_);
if (v___x_430_ == 0)
{
lean_dec(v_targetId_426_);
return v_bs_429_;
}
else
{
lean_object* v_v_431_; lean_object* v___x_432_; lean_object* v_bs_x27_433_; lean_object* v___y_435_; 
v_v_431_ = lean_array_uget(v_bs_429_, v_i_428_);
v___x_432_ = lean_unsigned_to_nat(0u);
v_bs_x27_433_ = lean_array_uset(v_bs_429_, v_i_428_, v___x_432_);
switch(lean_obj_tag(v_v_431_))
{
case 3:
{
lean_object* v_i_440_; lean_object* v_y_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_i_440_ = lean_ctor_get(v_v_431_, 1);
v_y_441_ = lean_ctor_get(v_v_431_, 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v_v_431_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v_v_431_, 0);
lean_dec(v_unused_449_);
v___x_443_ = v_v_431_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_y_441_);
lean_inc(v_i_440_);
lean_dec(v_v_431_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
lean_inc(v_targetId_426_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_targetId_426_);
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_targetId_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_i_440_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_y_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
v___y_435_ = v___x_446_;
goto v___jp_434_;
}
}
}
case 5:
{
lean_object* v_i_450_; lean_object* v_offset_451_; lean_object* v_y_452_; lean_object* v_ty_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_i_450_ = lean_ctor_get(v_v_431_, 1);
v_offset_451_ = lean_ctor_get(v_v_431_, 2);
v_y_452_ = lean_ctor_get(v_v_431_, 3);
v_ty_453_ = lean_ctor_get(v_v_431_, 4);
v_isSharedCheck_460_ = !lean_is_exclusive(v_v_431_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v_v_431_, 0);
lean_dec(v_unused_461_);
v___x_455_ = v_v_431_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_ty_453_);
lean_inc(v_y_452_);
lean_inc(v_offset_451_);
lean_inc(v_i_450_);
lean_dec(v_v_431_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
lean_inc(v_targetId_426_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v_targetId_426_);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_targetId_426_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_i_450_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_offset_451_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_y_452_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_ty_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
v___y_435_ = v___x_458_;
goto v___jp_434_;
}
}
}
case 4:
{
lean_object* v_i_462_; lean_object* v_y_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v_i_462_ = lean_ctor_get(v_v_431_, 1);
v_y_463_ = lean_ctor_get(v_v_431_, 2);
v_isSharedCheck_470_ = !lean_is_exclusive(v_v_431_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_v_431_, 0);
lean_dec(v_unused_471_);
v___x_465_ = v_v_431_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_y_463_);
lean_inc(v_i_462_);
lean_dec(v_v_431_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
lean_inc(v_targetId_426_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v_targetId_426_);
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_targetId_426_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_i_462_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_y_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
v___y_435_ = v___x_468_;
goto v___jp_434_;
}
}
}
default: 
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec(v_v_431_);
v___x_472_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2);
v___x_473_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(v___x_472_);
v___y_435_ = v___x_473_;
goto v___jp_434_;
}
}
v___jp_434_:
{
size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_428_, v___x_436_);
v___x_438_ = lean_array_uset(v_bs_x27_433_, v_i_428_, v___y_435_);
v_i_428_ = v___x_437_;
v_bs_429_ = v___x_438_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object* v_targetId_474_, lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_bs_477_){
_start:
{
size_t v_sz_boxed_478_; size_t v_i_boxed_479_; lean_object* v_res_480_; 
v_sz_boxed_478_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_479_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_474_, v_sz_boxed_478_, v_i_boxed_479_, v_bs_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object* v_targetId_481_, lean_object* v_sets_482_){
_start:
{
size_t v_sz_484_; size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_sz_484_ = lean_array_size(v_sets_482_);
v___x_485_ = ((size_t)0ULL);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_481_, v_sz_484_, v___x_485_, v_sets_482_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object* v_targetId_488_, lean_object* v_sets_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_488_, v_sets_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object* v_targetId_492_, lean_object* v_sets_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_492_, v_sets_493_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object* v_targetId_500_, lean_object* v_sets_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(v_targetId_500_, v_sets_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object* v_fvarId_508_, lean_object* v_i_509_, lean_object* v_y_510_, lean_object* v_a_511_){
_start:
{
if (lean_obj_tag(v_y_510_) == 0)
{
uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = 0;
v___x_514_ = lean_box(v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
else
{
lean_object* v_fvarId_516_; uint8_t v___x_517_; lean_object* v___x_518_; 
v_fvarId_516_ = lean_ctor_get(v_y_510_, 0);
v___x_517_ = 1;
v___x_518_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_517_, v_fvarId_516_, v_a_511_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_546_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_546_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_546_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_546_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
if (lean_obj_tag(v_a_519_) == 1)
{
lean_object* v_val_523_; 
v_val_523_ = lean_ctor_get(v_a_519_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v_a_519_, 1);
if (lean_obj_tag(v_val_523_) == 6)
{
lean_object* v_i_524_; lean_object* v_var_525_; uint8_t v___x_526_; 
v_i_524_ = lean_ctor_get(v_val_523_, 0);
lean_inc(v_i_524_);
v_var_525_ = lean_ctor_get(v_val_523_, 1);
lean_inc(v_var_525_);
lean_dec_ref_known(v_val_523_, 2);
v___x_526_ = lean_nat_dec_eq(v_i_509_, v_i_524_);
lean_dec(v_i_524_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec(v_var_525_);
v___x_527_ = lean_box(v___x_526_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_527_);
v___x_529_ = v___x_521_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_531_ = l_Lean_instBEqFVarId_beq(v_fvarId_508_, v_var_525_);
lean_dec(v_var_525_);
v___x_532_ = lean_box(v___x_531_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_532_);
v___x_534_ = v___x_521_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
uint8_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
lean_dec(v_val_523_);
v___x_536_ = 0;
v___x_537_ = lean_box(v___x_536_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_537_);
v___x_539_ = v___x_521_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
lean_dec(v_a_519_);
v___x_541_ = 0;
v___x_542_ = lean_box(v___x_541_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_542_);
v___x_544_ = v___x_521_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_518_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_518_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object* v_fvarId_555_, lean_object* v_i_556_, lean_object* v_y_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_555_, v_i_556_, v_y_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec(v_y_557_);
lean_dec(v_i_556_);
lean_dec(v_fvarId_555_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object* v_fvarId_561_, lean_object* v_i_562_, lean_object* v_y_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_561_, v_i_562_, v_y_563_, v_a_565_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object* v_fvarId_570_, lean_object* v_i_571_, lean_object* v_y_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(v_fvarId_570_, v_i_571_, v_y_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_y_572_);
lean_dec(v_i_571_);
lean_dec(v_fvarId_570_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object* v_fvarId_579_, lean_object* v_i_580_, lean_object* v_y_581_, lean_object* v_a_582_){
_start:
{
uint8_t v___x_584_; lean_object* v___x_585_; 
v___x_584_ = 1;
v___x_585_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_584_, v_y_581_, v_a_582_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_613_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_613_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_613_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_613_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
if (lean_obj_tag(v_a_586_) == 1)
{
lean_object* v_val_590_; 
v_val_590_ = lean_ctor_get(v_a_586_, 0);
lean_inc(v_val_590_);
lean_dec_ref_known(v_a_586_, 1);
if (lean_obj_tag(v_val_590_) == 7)
{
lean_object* v_i_591_; lean_object* v_var_592_; uint8_t v___x_593_; 
v_i_591_ = lean_ctor_get(v_val_590_, 0);
lean_inc(v_i_591_);
v_var_592_ = lean_ctor_get(v_val_590_, 1);
lean_inc(v_var_592_);
lean_dec_ref_known(v_val_590_, 2);
v___x_593_ = lean_nat_dec_eq(v_i_580_, v_i_591_);
lean_dec(v_i_591_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_596_; 
lean_dec(v_var_592_);
v___x_594_ = lean_box(v___x_593_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_594_);
v___x_596_ = v___x_588_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
else
{
uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_598_ = l_Lean_instBEqFVarId_beq(v_fvarId_579_, v_var_592_);
lean_dec(v_var_592_);
v___x_599_ = lean_box(v___x_598_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_599_);
v___x_601_ = v___x_588_;
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
else
{
uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
lean_dec(v_val_590_);
v___x_603_ = 0;
v___x_604_ = lean_box(v___x_603_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_604_);
v___x_606_ = v___x_588_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec(v_a_586_);
v___x_608_ = 0;
v___x_609_ = lean_box(v___x_608_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_609_);
v___x_611_ = v___x_588_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_a_614_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_585_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_585_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object* v_fvarId_622_, lean_object* v_i_623_, lean_object* v_y_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_622_, v_i_623_, v_y_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec(v_y_624_);
lean_dec(v_i_623_);
lean_dec(v_fvarId_622_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object* v_fvarId_628_, lean_object* v_i_629_, lean_object* v_y_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_628_, v_i_629_, v_y_630_, v_a_632_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object* v_fvarId_637_, lean_object* v_i_638_, lean_object* v_y_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(v_fvarId_637_, v_i_638_, v_y_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_y_639_);
lean_dec(v_i_638_);
lean_dec(v_fvarId_637_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object* v_fvarId_646_, lean_object* v_i_647_, lean_object* v_offset_648_, lean_object* v_y_649_, lean_object* v_a_650_){
_start:
{
uint8_t v___x_652_; lean_object* v___x_653_; 
v___x_652_ = 1;
v___x_653_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_652_, v_y_649_, v_a_650_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_687_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_687_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_687_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_687_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
if (lean_obj_tag(v_a_654_) == 1)
{
lean_object* v_val_658_; 
v_val_658_ = lean_ctor_get(v_a_654_, 0);
lean_inc(v_val_658_);
lean_dec_ref_known(v_a_654_, 1);
if (lean_obj_tag(v_val_658_) == 8)
{
lean_object* v_n_659_; lean_object* v_offset_660_; lean_object* v_var_661_; uint8_t v___x_662_; 
v_n_659_ = lean_ctor_get(v_val_658_, 0);
lean_inc(v_n_659_);
v_offset_660_ = lean_ctor_get(v_val_658_, 1);
lean_inc(v_offset_660_);
v_var_661_ = lean_ctor_get(v_val_658_, 2);
lean_inc(v_var_661_);
lean_dec_ref_known(v_val_658_, 3);
v___x_662_ = lean_nat_dec_eq(v_i_647_, v_n_659_);
lean_dec(v_n_659_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_665_; 
lean_dec(v_var_661_);
lean_dec(v_offset_660_);
v___x_663_ = lean_box(v___x_662_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_663_);
v___x_665_ = v___x_656_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
else
{
uint8_t v___x_667_; 
v___x_667_ = lean_nat_dec_eq(v_offset_648_, v_offset_660_);
lean_dec(v_offset_660_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_670_; 
lean_dec(v_var_661_);
v___x_668_ = lean_box(v___x_667_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_668_);
v___x_670_ = v___x_656_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
else
{
uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_672_ = l_Lean_instBEqFVarId_beq(v_fvarId_646_, v_var_661_);
lean_dec(v_var_661_);
v___x_673_ = lean_box(v___x_672_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_673_);
v___x_675_ = v___x_656_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
lean_dec(v_val_658_);
v___x_677_ = 0;
v___x_678_ = lean_box(v___x_677_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_678_);
v___x_680_ = v___x_656_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
else
{
uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
lean_dec(v_a_654_);
v___x_682_ = 0;
v___x_683_ = lean_box(v___x_682_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_683_);
v___x_685_ = v___x_656_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_a_688_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_653_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_653_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object* v_fvarId_696_, lean_object* v_i_697_, lean_object* v_offset_698_, lean_object* v_y_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_696_, v_i_697_, v_offset_698_, v_y_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec(v_y_699_);
lean_dec(v_offset_698_);
lean_dec(v_i_697_);
lean_dec(v_fvarId_696_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object* v_fvarId_703_, lean_object* v_i_704_, lean_object* v_offset_705_, lean_object* v_y_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_703_, v_i_704_, v_offset_705_, v_y_706_, v_a_708_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object* v_fvarId_713_, lean_object* v_i_714_, lean_object* v_offset_715_, lean_object* v_y_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(v_fvarId_713_, v_i_714_, v_offset_715_, v_y_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_y_716_);
lean_dec(v_offset_715_);
lean_dec(v_i_714_);
lean_dec(v_fvarId_713_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_toApplicative_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_765_; 
v___x_729_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_730_ = l_StateRefT_x27_instMonad___redArg(v___x_729_);
v_toApplicative_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_730_, 1);
lean_dec(v_unused_766_);
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_765_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_toApplicative_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_765_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_toFunctor_735_; lean_object* v_toSeq_736_; lean_object* v_toSeqLeft_737_; lean_object* v_toSeqRight_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_763_; 
v_toFunctor_735_ = lean_ctor_get(v_toApplicative_731_, 0);
v_toSeq_736_ = lean_ctor_get(v_toApplicative_731_, 2);
v_toSeqLeft_737_ = lean_ctor_get(v_toApplicative_731_, 3);
v_toSeqRight_738_ = lean_ctor_get(v_toApplicative_731_, 4);
v_isSharedCheck_763_ = !lean_is_exclusive(v_toApplicative_731_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v_toApplicative_731_, 1);
lean_dec(v_unused_764_);
v___x_740_ = v_toApplicative_731_;
v_isShared_741_ = v_isSharedCheck_763_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_toSeqRight_738_);
lean_inc(v_toSeqLeft_737_);
lean_inc(v_toSeq_736_);
lean_inc(v_toFunctor_735_);
lean_dec(v_toApplicative_731_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_763_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___x_751_; 
v___f_742_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_743_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_735_);
v___f_744_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_744_, 0, v_toFunctor_735_);
v___f_745_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_745_, 0, v_toFunctor_735_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___f_744_);
lean_ctor_set(v___x_746_, 1, v___f_745_);
v___f_747_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_747_, 0, v_toSeqRight_738_);
v___f_748_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_748_, 0, v_toSeqLeft_737_);
v___f_749_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_749_, 0, v_toSeq_736_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 4, v___f_747_);
lean_ctor_set(v___x_740_, 3, v___f_748_);
lean_ctor_set(v___x_740_, 2, v___f_749_);
lean_ctor_set(v___x_740_, 1, v___f_742_);
lean_ctor_set(v___x_740_, 0, v___x_746_);
v___x_751_ = v___x_740_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___f_742_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v___f_749_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v___f_748_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v___f_747_);
v___x_751_ = v_reuseFailAlloc_762_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v___f_743_);
lean_ctor_set(v___x_733_, 0, v___x_751_);
v___x_753_ = v___x_733_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___f_743_);
v___x_753_ = v_reuseFailAlloc_761_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___f_758_; lean_object* v___x_883__overap_759_; lean_object* v___x_760_; 
v___x_754_ = l_StateRefT_x27_instMonad___redArg(v___x_753_);
v___x_755_ = 0;
v___x_756_ = lean_box(v___x_755_);
v___x_757_ = l_instInhabitedOfMonad___redArg(v___x_754_, v___x_756_);
v___f_758_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_758_, 0, v___x_757_);
v___x_883__overap_759_ = lean_panic_fn_borrowed(v___f_758_, v_msg_723_);
lean_dec_ref(v___f_758_);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
v___x_760_ = lean_apply_5(v___x_883__overap_759_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, lean_box(0));
return v___x_760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object* v_msg_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v_msg_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_773_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_776_ = lean_unsigned_to_nat(13u);
v___x_777_ = lean_unsigned_to_nat(174u);
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0));
v___x_779_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_780_ = l_mkPanicMessageWithDecl(v___x_779_, v___x_778_, v___x_777_, v___x_776_, v___x_775_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object* v_selfId_781_, lean_object* v_as_782_, size_t v_sz_783_, size_t v_i_784_, lean_object* v_b_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_a_792_; uint8_t v___x_796_; 
v___x_796_ = lean_usize_dec_lt(v_i_784_, v_sz_783_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; 
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v_b_785_);
return v___x_797_;
}
else
{
lean_object* v_fst_798_; lean_object* v_snd_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_836_; 
v_fst_798_ = lean_ctor_get(v_b_785_, 0);
v_snd_799_ = lean_ctor_get(v_b_785_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_b_785_);
if (v_isSharedCheck_836_ == 0)
{
v___x_801_ = v_b_785_;
v_isShared_802_ = v_isSharedCheck_836_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_snd_799_);
lean_inc(v_fst_798_);
lean_dec(v_b_785_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_836_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_a_803_; lean_object* v___y_805_; 
v_a_803_ = lean_array_uget_borrowed(v_as_782_, v_i_784_);
switch(lean_obj_tag(v_a_803_))
{
case 3:
{
lean_object* v_i_824_; lean_object* v_y_825_; lean_object* v___x_826_; 
v_i_824_ = lean_ctor_get(v_a_803_, 1);
v_y_825_ = lean_ctor_get(v_a_803_, 2);
v___x_826_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_selfId_781_, v_i_824_, v_y_825_, v___y_787_);
v___y_805_ = v___x_826_;
goto v___jp_804_;
}
case 4:
{
lean_object* v_i_827_; lean_object* v_y_828_; lean_object* v___x_829_; 
v_i_827_ = lean_ctor_get(v_a_803_, 1);
v_y_828_ = lean_ctor_get(v_a_803_, 2);
v___x_829_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_selfId_781_, v_i_827_, v_y_828_, v___y_787_);
v___y_805_ = v___x_829_;
goto v___jp_804_;
}
case 5:
{
lean_object* v_i_830_; lean_object* v_offset_831_; lean_object* v_y_832_; lean_object* v___x_833_; 
v_i_830_ = lean_ctor_get(v_a_803_, 1);
v_offset_831_ = lean_ctor_get(v_a_803_, 2);
v_y_832_ = lean_ctor_get(v_a_803_, 3);
v___x_833_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_selfId_781_, v_i_830_, v_offset_831_, v_y_832_, v___y_787_);
v___y_805_ = v___x_833_;
goto v___jp_804_;
}
default: 
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1);
v___x_835_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v___x_834_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
v___y_805_ = v___x_835_;
goto v___jp_804_;
}
}
v___jp_804_:
{
if (lean_obj_tag(v___y_805_) == 0)
{
lean_object* v_a_806_; uint8_t v___x_807_; 
v_a_806_ = lean_ctor_get(v___y_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___y_805_, 1);
v___x_807_ = lean_unbox(v_a_806_);
lean_dec(v_a_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_inc(v_a_803_);
v___x_808_ = lean_array_push(v_fst_798_, v_a_803_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_808_);
v___x_810_ = v___x_801_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_snd_799_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
v_a_792_ = v___x_810_;
goto v___jp_791_;
}
}
else
{
lean_object* v___x_812_; lean_object* v___x_814_; 
lean_inc(v_a_803_);
v___x_812_ = lean_array_push(v_snd_799_, v_a_803_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_812_);
v___x_814_ = v___x_801_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_fst_798_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
v_a_792_ = v___x_814_;
goto v___jp_791_;
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_del_object(v___x_801_);
lean_dec(v_snd_799_);
lean_dec(v_fst_798_);
v_a_816_ = lean_ctor_get(v___y_805_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___y_805_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___y_805_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___y_805_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
v___jp_791_:
{
size_t v___x_793_; size_t v___x_794_; 
v___x_793_ = ((size_t)1ULL);
v___x_794_ = lean_usize_add(v_i_784_, v___x_793_);
v_i_784_ = v___x_794_;
v_b_785_ = v_a_792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object* v_selfId_837_, lean_object* v_as_838_, lean_object* v_sz_839_, lean_object* v_i_840_, lean_object* v_b_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
size_t v_sz_boxed_847_; size_t v_i_boxed_848_; lean_object* v_res_849_; 
v_sz_boxed_847_ = lean_unbox_usize(v_sz_839_);
lean_dec(v_sz_839_);
v_i_boxed_848_ = lean_unbox_usize(v_i_840_);
lean_dec(v_i_840_);
v_res_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_837_, v_as_838_, v_sz_boxed_847_, v_i_boxed_848_, v_b_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec_ref(v_as_838_);
lean_dec(v_selfId_837_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object* v_selfId_852_, lean_object* v_sets_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v___x_859_; size_t v_sz_860_; size_t v___x_861_; lean_object* v___x_862_; 
v___x_859_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0));
v_sz_860_ = lean_array_size(v_sets_853_);
v___x_861_ = ((size_t)0ULL);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_852_, v_sets_853_, v_sz_860_, v___x_861_, v___x_859_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_879_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_879_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_879_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_879_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_fst_867_; lean_object* v_snd_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_878_; 
v_fst_867_ = lean_ctor_get(v_a_863_, 0);
v_snd_868_ = lean_ctor_get(v_a_863_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_a_863_);
if (v_isSharedCheck_878_ == 0)
{
v___x_870_ = v_a_863_;
v_isShared_871_ = v_isSharedCheck_878_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_snd_868_);
lean_inc(v_fst_867_);
lean_dec(v_a_863_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_878_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v_fst_867_);
lean_ctor_set(v___x_870_, 0, v_snd_868_);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_snd_868_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_fst_867_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_873_);
v___x_875_ = v___x_865_;
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
}
}
else
{
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object* v_selfId_880_, lean_object* v_sets_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_selfId_880_, v_sets_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec_ref(v_sets_881_);
lean_dec(v_selfId_880_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object* v_target_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_snd_891_; 
v_snd_891_ = lean_ctor_get(v_a_889_, 1);
lean_inc(v_snd_891_);
switch(lean_obj_tag(v_snd_891_))
{
case 7:
{
lean_object* v_fst_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_910_; 
v_fst_892_ = lean_ctor_get(v_a_889_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_a_889_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v_a_889_, 1);
lean_dec(v_unused_911_);
v___x_894_ = v_a_889_;
v_isShared_895_ = v_isSharedCheck_910_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_fst_892_);
lean_dec(v_a_889_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_910_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_fvarId_896_; lean_object* v_k_897_; uint8_t v___x_898_; 
v_fvarId_896_ = lean_ctor_get(v_snd_891_, 0);
v_k_897_ = lean_ctor_get(v_snd_891_, 3);
v___x_898_ = l_Lean_instBEqFVarId_beq(v_target_888_, v_fvarId_896_);
if (v___x_898_ == 0)
{
lean_object* v___x_900_; 
if (v_isShared_895_ == 0)
{
v___x_900_ = v___x_894_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_fst_892_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_snd_891_);
v___x_900_ = v_reuseFailAlloc_902_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
else
{
uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
lean_inc_ref(v_k_897_);
v___x_903_ = 1;
v___x_904_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_903_, v_snd_891_);
lean_dec_ref_known(v_snd_891_, 4);
v___x_905_ = lean_array_push(v_fst_892_, v___x_904_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v_k_897_);
lean_ctor_set(v___x_894_, 0, v___x_905_);
v___x_907_ = v___x_894_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_k_897_);
v___x_907_ = v_reuseFailAlloc_909_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
v_a_889_ = v___x_907_;
goto _start;
}
}
}
}
case 9:
{
lean_object* v_fst_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_930_; 
v_fst_912_ = lean_ctor_get(v_a_889_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_a_889_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_a_889_, 1);
lean_dec(v_unused_931_);
v___x_914_ = v_a_889_;
v_isShared_915_ = v_isSharedCheck_930_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_fst_912_);
lean_dec(v_a_889_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_930_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_fvarId_916_; lean_object* v_k_917_; uint8_t v___x_918_; 
v_fvarId_916_ = lean_ctor_get(v_snd_891_, 0);
v_k_917_ = lean_ctor_get(v_snd_891_, 5);
v___x_918_ = l_Lean_instBEqFVarId_beq(v_target_888_, v_fvarId_916_);
if (v___x_918_ == 0)
{
lean_object* v___x_920_; 
if (v_isShared_915_ == 0)
{
v___x_920_ = v___x_914_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_fst_912_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_snd_891_);
v___x_920_ = v_reuseFailAlloc_922_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; 
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
else
{
uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
lean_inc_ref(v_k_917_);
v___x_923_ = 1;
v___x_924_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_923_, v_snd_891_);
lean_dec_ref_known(v_snd_891_, 6);
v___x_925_ = lean_array_push(v_fst_912_, v___x_924_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v_k_917_);
lean_ctor_set(v___x_914_, 0, v___x_925_);
v___x_927_ = v___x_914_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_k_917_);
v___x_927_ = v_reuseFailAlloc_929_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
v_a_889_ = v___x_927_;
goto _start;
}
}
}
}
case 8:
{
lean_object* v_fst_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_950_; 
v_fst_932_ = lean_ctor_get(v_a_889_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_889_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_a_889_, 1);
lean_dec(v_unused_951_);
v___x_934_ = v_a_889_;
v_isShared_935_ = v_isSharedCheck_950_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_fst_932_);
lean_dec(v_a_889_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_950_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_fvarId_936_; lean_object* v_k_937_; uint8_t v___x_938_; 
v_fvarId_936_ = lean_ctor_get(v_snd_891_, 0);
v_k_937_ = lean_ctor_get(v_snd_891_, 3);
v___x_938_ = l_Lean_instBEqFVarId_beq(v_target_888_, v_fvarId_936_);
if (v___x_938_ == 0)
{
lean_object* v___x_940_; 
if (v_isShared_935_ == 0)
{
v___x_940_ = v___x_934_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_fst_932_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_snd_891_);
v___x_940_ = v_reuseFailAlloc_942_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
else
{
uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
lean_inc_ref(v_k_937_);
v___x_943_ = 1;
v___x_944_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_943_, v_snd_891_);
lean_dec_ref_known(v_snd_891_, 4);
v___x_945_ = lean_array_push(v_fst_932_, v___x_944_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 1, v_k_937_);
lean_ctor_set(v___x_934_, 0, v___x_945_);
v___x_947_ = v___x_934_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_k_937_);
v___x_947_ = v_reuseFailAlloc_949_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
v_a_889_ = v___x_947_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_fst_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_960_; 
v_fst_952_ = lean_ctor_get(v_a_889_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_a_889_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v_a_889_, 1);
lean_dec(v_unused_961_);
v___x_954_ = v_a_889_;
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_fst_952_);
lean_dec(v_a_889_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_snd_891_);
v___x_957_ = v_reuseFailAlloc_959_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object* v_target_962_, lean_object* v_a_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_962_, v_a_963_);
lean_dec(v_target_962_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object* v_target_966_, lean_object* v_k_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_sets_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_sets_973_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_sets_973_);
lean_ctor_set(v___x_974_, 1, v_k_967_);
v___x_975_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_966_, v___x_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_992_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_992_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_992_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_992_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_fst_980_; lean_object* v_snd_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_991_; 
v_fst_980_ = lean_ctor_get(v_a_976_, 0);
v_snd_981_ = lean_ctor_get(v_a_976_, 1);
v_isSharedCheck_991_ = !lean_is_exclusive(v_a_976_);
if (v_isSharedCheck_991_ == 0)
{
v___x_983_ = v_a_976_;
v_isShared_984_ = v_isSharedCheck_991_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snd_981_);
lean_inc(v_fst_980_);
lean_dec(v_a_976_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_991_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_fst_980_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_snd_981_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_986_);
v___x_988_ = v___x_978_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
else
{
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object* v_target_993_, lean_object* v_k_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_target_993_, v_k_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_target_993_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object* v_target_1001_, lean_object* v_inst_1002_, lean_object* v_a_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_1001_, v_a_1003_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object* v_target_1010_, lean_object* v_inst_1011_, lean_object* v_a_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(v_target_1010_, v_inst_1011_, v_a_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v_target_1010_);
return v_res_1018_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3));
v___x_1027_ = l_Lean_Expr_const___override(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1028_, lean_object* v_mask_1029_, lean_object* v_origAllocId_1030_, lean_object* v_a_1031_, lean_object* v_b_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_a_1039_; uint8_t v___x_1043_; 
v___x_1043_ = lean_nat_dec_lt(v_a_1031_, v_upperBound_1028_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
lean_dec(v_a_1031_);
lean_dec(v_origAllocId_1030_);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v_b_1032_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_array_fget_borrowed(v_mask_1029_, v_a_1031_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1));
v___x_1047_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1046_, v___y_1034_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v___x_1049_ = 1;
v___x_1050_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_origAllocId_1030_);
lean_inc(v_a_1031_);
v___x_1051_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_a_1031_);
lean_ctor_set(v___x_1051_, 1, v_origAllocId_1030_);
v___x_1052_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1049_, v_a_1048_, v___x_1050_, v___x_1051_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v_fvarId_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v_fvarId_1054_ = lean_ctor_get(v_a_1053_, 0);
v___x_1055_ = 0;
v___x_1056_ = lean_unsigned_to_nat(1u);
v___x_1057_ = lean_box(0);
lean_inc(v_fvarId_1054_);
v___x_1058_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1058_, 0, v_fvarId_1054_);
lean_ctor_set(v___x_1058_, 1, v___x_1056_);
lean_ctor_set(v___x_1058_, 2, v___x_1057_);
lean_ctor_set(v___x_1058_, 3, v_b_1032_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*4, v___x_1043_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*4 + 1, v___x_1055_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_a_1053_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v_a_1039_ = v___x_1059_;
goto v___jp_1038_;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec_ref(v_b_1032_);
lean_dec(v_a_1031_);
lean_dec(v_origAllocId_1030_);
v_a_1060_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1052_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1052_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v_b_1032_);
lean_dec(v_a_1031_);
lean_dec(v_origAllocId_1030_);
v_a_1068_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1047_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1047_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
v_a_1039_ = v_b_1032_;
goto v___jp_1038_;
}
}
v___jp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = lean_nat_add(v_a_1031_, v___x_1040_);
lean_dec(v_a_1031_);
v_a_1031_ = v___x_1041_;
v_b_1032_ = v_a_1039_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1076_, lean_object* v_mask_1077_, lean_object* v_origAllocId_1078_, lean_object* v_a_1079_, lean_object* v_b_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1076_, v_mask_1077_, v_origAllocId_1078_, v_a_1079_, v_b_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v_mask_1077_);
lean_dec(v_upperBound_1076_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object* v_origAllocId_1087_, lean_object* v_mask_1088_, lean_object* v_resetJpId_1089_, lean_object* v_isSharedId_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_code_1104_; lean_object* v___x_1105_; 
lean_inc(v_origAllocId_1087_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_origAllocId_1087_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_isSharedId_1090_);
v___x_1098_ = lean_unsigned_to_nat(0u);
v___x_1099_ = lean_array_get_size(v_mask_1088_);
v___x_1100_ = lean_unsigned_to_nat(2u);
v___x_1101_ = lean_mk_empty_array_with_capacity(v___x_1100_);
v___x_1102_ = lean_array_push(v___x_1101_, v___x_1096_);
v___x_1103_ = lean_array_push(v___x_1102_, v___x_1097_);
v_code_1104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1104_, 0, v_resetJpId_1089_);
lean_ctor_set(v_code_1104_, 1, v___x_1103_);
v___x_1105_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v___x_1099_, v_mask_1088_, v_origAllocId_1087_, v___x_1098_, v_code_1104_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object* v_origAllocId_1106_, lean_object* v_mask_1107_, lean_object* v_resetJpId_1108_, lean_object* v_isSharedId_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_1106_, v_mask_1107_, v_resetJpId_1108_, v_isSharedId_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec_ref(v_mask_1107_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object* v_upperBound_1116_, lean_object* v_mask_1117_, lean_object* v_origAllocId_1118_, lean_object* v_inst_1119_, lean_object* v_R_1120_, lean_object* v_a_1121_, lean_object* v_b_1122_, lean_object* v_c_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1116_, v_mask_1117_, v_origAllocId_1118_, v_a_1121_, v_b_1122_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1130_, lean_object* v_mask_1131_, lean_object* v_origAllocId_1132_, lean_object* v_inst_1133_, lean_object* v_R_1134_, lean_object* v_a_1135_, lean_object* v_b_1136_, lean_object* v_c_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(v_upperBound_1130_, v_mask_1131_, v_origAllocId_1132_, v_inst_1133_, v_R_1134_, v_a_1135_, v_b_1136_, v_c_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec_ref(v_mask_1131_);
lean_dec(v_upperBound_1130_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object* v_as_1144_, size_t v_sz_1145_, size_t v_i_1146_, lean_object* v_b_1147_){
_start:
{
lean_object* v_a_1150_; uint8_t v___x_1154_; 
v___x_1154_ = lean_usize_dec_lt(v_i_1146_, v_sz_1145_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_b_1147_);
return v___x_1155_;
}
else
{
lean_object* v_a_1156_; 
v_a_1156_ = lean_array_uget_borrowed(v_as_1144_, v_i_1146_);
if (lean_obj_tag(v_a_1156_) == 1)
{
lean_object* v_val_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; 
v_val_1157_ = lean_ctor_get(v_a_1156_, 0);
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = 0;
lean_inc(v_val_1157_);
v___x_1160_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1160_, 0, v_val_1157_);
lean_ctor_set(v___x_1160_, 1, v___x_1158_);
lean_ctor_set(v___x_1160_, 2, v_b_1147_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*3, v___x_1154_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*3 + 1, v___x_1159_);
v_a_1150_ = v___x_1160_;
goto v___jp_1149_;
}
else
{
v_a_1150_ = v_b_1147_;
goto v___jp_1149_;
}
}
v___jp_1149_:
{
size_t v___x_1151_; size_t v___x_1152_; 
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_add(v_i_1146_, v___x_1151_);
v_i_1146_ = v___x_1152_;
v_b_1147_ = v_a_1150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object* v_as_1161_, lean_object* v_sz_1162_, lean_object* v_i_1163_, lean_object* v_b_1164_, lean_object* v___y_1165_){
_start:
{
size_t v_sz_boxed_1166_; size_t v_i_boxed_1167_; lean_object* v_res_1168_; 
v_sz_boxed_1166_ = lean_unbox_usize(v_sz_1162_);
lean_dec(v_sz_1162_);
v_i_boxed_1167_ = lean_unbox_usize(v_i_1163_);
lean_dec(v_i_1163_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1161_, v_sz_boxed_1166_, v_i_boxed_1167_, v_b_1164_);
lean_dec_ref(v_as_1161_);
return v_res_1168_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_unsigned_to_nat(2u);
v___x_1171_ = lean_mk_empty_array_with_capacity(v___x_1170_);
v___x_1172_ = lean_array_push(v___x_1171_, v___x_1169_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object* v_origAllocId_1173_, lean_object* v_mask_1174_, lean_object* v_resetJpId_1175_, lean_object* v_isSharedId_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v_code_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v_code_1190_; size_t v_sz_1191_; size_t v___x_1192_; lean_object* v___x_1193_; 
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_isSharedId_1176_);
v___x_1183_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0);
v___x_1184_ = lean_array_push(v___x_1183_, v___x_1182_);
v_code_1185_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1185_, 0, v_resetJpId_1175_);
lean_ctor_set(v_code_1185_, 1, v___x_1184_);
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = 1;
v___x_1188_ = 0;
v___x_1189_ = lean_box(0);
v_code_1190_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_code_1190_, 0, v_origAllocId_1173_);
lean_ctor_set(v_code_1190_, 1, v___x_1186_);
lean_ctor_set(v_code_1190_, 2, v___x_1189_);
lean_ctor_set(v_code_1190_, 3, v_code_1185_);
lean_ctor_set_uint8(v_code_1190_, sizeof(void*)*4, v___x_1187_);
lean_ctor_set_uint8(v_code_1190_, sizeof(void*)*4 + 1, v___x_1188_);
v_sz_1191_ = lean_array_size(v_mask_1174_);
v___x_1192_ = ((size_t)0ULL);
v___x_1193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_mask_1174_, v_sz_1191_, v___x_1192_, v_code_1190_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(lean_object* v_origAllocId_1194_, lean_object* v_mask_1195_, lean_object* v_resetJpId_1196_, lean_object* v_isSharedId_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_1194_, v_mask_1195_, v_resetJpId_1196_, v_isSharedId_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec_ref(v_mask_1195_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(lean_object* v_as_1204_, size_t v_sz_1205_, size_t v_i_1206_, lean_object* v_b_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1204_, v_sz_1205_, v_i_1206_, v_b_1207_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(lean_object* v_as_1214_, lean_object* v_sz_1215_, lean_object* v_i_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
size_t v_sz_boxed_1223_; size_t v_i_boxed_1224_; lean_object* v_res_1225_; 
v_sz_boxed_1223_ = lean_unbox_usize(v_sz_1215_);
lean_dec(v_sz_1215_);
v_i_boxed_1224_ = lean_unbox_usize(v_i_1216_);
lean_dec(v_i_1216_);
v_res_1225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(v_as_1214_, v_sz_boxed_1223_, v_i_boxed_1224_, v_b_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v_as_1214_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1226_, lean_object* v_args_1227_, lean_object* v_origAllocId_1228_, lean_object* v_resetTokenId_1229_, lean_object* v_a_1230_, lean_object* v_b_1231_, lean_object* v___y_1232_){
_start:
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_lt(v_a_1230_, v_upperBound_1226_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_a_1230_);
lean_dec(v_resetTokenId_1229_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_b_1231_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_array_fget_borrowed(v_args_1227_, v_a_1230_);
v___x_1237_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_origAllocId_1228_, v_a_1230_, v___x_1236_, v___y_1232_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v_a_1240_; uint8_t v___x_1244_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1244_ = lean_unbox(v_a_1238_);
lean_dec(v_a_1238_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_inc(v___x_1236_);
lean_inc(v_a_1230_);
lean_inc(v_resetTokenId_1229_);
v___x_1245_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1245_, 0, v_resetTokenId_1229_);
lean_ctor_set(v___x_1245_, 1, v_a_1230_);
lean_ctor_set(v___x_1245_, 2, v___x_1236_);
lean_ctor_set(v___x_1245_, 3, v_b_1231_);
v_a_1240_ = v___x_1245_;
goto v___jp_1239_;
}
else
{
v_a_1240_ = v_b_1231_;
goto v___jp_1239_;
}
v___jp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_add(v_a_1230_, v___x_1241_);
lean_dec(v_a_1230_);
v_a_1230_ = v___x_1242_;
v_b_1231_ = v_a_1240_;
goto _start;
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_b_1231_);
lean_dec(v_a_1230_);
lean_dec(v_resetTokenId_1229_);
v_a_1246_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1237_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1237_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1254_, lean_object* v_args_1255_, lean_object* v_origAllocId_1256_, lean_object* v_resetTokenId_1257_, lean_object* v_a_1258_, lean_object* v_b_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1254_, v_args_1255_, v_origAllocId_1256_, v_resetTokenId_1257_, v_a_1258_, v_b_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec(v_origAllocId_1256_);
lean_dec_ref(v_args_1255_);
lean_dec(v_upperBound_1254_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(lean_object* v_resetTokenId_1263_, lean_object* v_info_1264_, uint8_t v_update_1265_, lean_object* v_args_1266_, lean_object* v_contJpId_1267_, lean_object* v_origAllocId_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v_code_1280_; lean_object* v___x_1281_; 
lean_inc_n(v_resetTokenId_1263_, 2);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_resetTokenId_1263_);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = lean_array_get_size(v_args_1266_);
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_mk_empty_array_with_capacity(v___x_1277_);
v___x_1279_ = lean_array_push(v___x_1278_, v___x_1274_);
v_code_1280_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1280_, 0, v_contJpId_1267_);
lean_ctor_set(v_code_1280_, 1, v___x_1279_);
v___x_1281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v___x_1276_, v_args_1266_, v_origAllocId_1268_, v_resetTokenId_1263_, v___x_1275_, v_code_1280_, v_a_1270_);
if (lean_obj_tag(v___x_1281_) == 0)
{
if (v_update_1265_ == 0)
{
lean_dec(v_resetTokenId_1263_);
return v___x_1281_;
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1291_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1291_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1291_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_cidx_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v_cidx_1286_ = lean_ctor_get(v_info_1264_, 1);
lean_inc(v_cidx_1286_);
v___x_1287_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1287_, 0, v_resetTokenId_1263_);
lean_ctor_set(v___x_1287_, 1, v_cidx_1286_);
lean_ctor_set(v___x_1287_, 2, v_a_1282_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1287_);
v___x_1289_ = v___x_1284_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_dec(v_resetTokenId_1263_);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(lean_object* v_resetTokenId_1292_, lean_object* v_info_1293_, lean_object* v_update_1294_, lean_object* v_args_1295_, lean_object* v_contJpId_1296_, lean_object* v_origAllocId_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
uint8_t v_update_boxed_1303_; lean_object* v_res_1304_; 
v_update_boxed_1303_ = lean_unbox(v_update_1294_);
v_res_1304_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1292_, v_info_1293_, v_update_boxed_1303_, v_args_1295_, v_contJpId_1296_, v_origAllocId_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_origAllocId_1297_);
lean_dec_ref(v_args_1295_);
lean_dec_ref(v_info_1293_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(lean_object* v_upperBound_1305_, lean_object* v_args_1306_, lean_object* v_origAllocId_1307_, lean_object* v_resetTokenId_1308_, lean_object* v_inst_1309_, lean_object* v_R_1310_, lean_object* v_a_1311_, lean_object* v_b_1312_, lean_object* v_c_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1305_, v_args_1306_, v_origAllocId_1307_, v_resetTokenId_1308_, v_a_1311_, v_b_1312_, v___y_1315_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1320_, lean_object* v_args_1321_, lean_object* v_origAllocId_1322_, lean_object* v_resetTokenId_1323_, lean_object* v_inst_1324_, lean_object* v_R_1325_, lean_object* v_a_1326_, lean_object* v_b_1327_, lean_object* v_c_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(v_upperBound_1320_, v_args_1321_, v_origAllocId_1322_, v_resetTokenId_1323_, v_inst_1324_, v_R_1325_, v_a_1326_, v_b_1327_, v_c_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v_origAllocId_1322_);
lean_dec_ref(v_args_1321_);
lean_dec(v_upperBound_1320_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(lean_object* v_decl_1338_, lean_object* v_info_1339_, lean_object* v_args_1340_, lean_object* v_contJpId_1341_, lean_object* v_selfSets_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1));
v___x_1349_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1348_, v_a_1344_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v_type_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v_type_1351_ = lean_ctor_get(v_decl_1338_, 2);
lean_inc_ref(v_type_1351_);
lean_dec_ref(v_decl_1338_);
v___x_1352_ = 1;
v___x_1353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_info_1339_);
lean_ctor_set(v___x_1353_, 1, v_args_1340_);
v___x_1354_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1352_, v_a_1350_, v_type_1351_, v___x_1353_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v_fvarId_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1372_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v_fvarId_1356_ = lean_ctor_get(v_a_1355_, 0);
lean_inc_n(v_fvarId_1356_, 2);
v___x_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_fvarId_1356_);
v___x_1358_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_fvarId_1356_, v_selfSets_1342_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1372_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1372_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1363_ = lean_unsigned_to_nat(1u);
v___x_1364_ = lean_mk_empty_array_with_capacity(v___x_1363_);
v___x_1365_ = lean_array_push(v___x_1364_, v___x_1357_);
v___x_1366_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_contJpId_1341_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1352_, v_a_1359_, v___x_1366_);
lean_dec(v_a_1359_);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v_a_1355_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1368_);
v___x_1370_ = v___x_1361_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v_selfSets_1342_);
lean_dec(v_contJpId_1341_);
v_a_1373_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1354_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1354_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v_selfSets_1342_);
lean_dec(v_contJpId_1341_);
lean_dec_ref(v_args_1340_);
lean_dec_ref(v_info_1339_);
lean_dec_ref(v_decl_1338_);
v_a_1381_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1349_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1349_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(lean_object* v_decl_1389_, lean_object* v_info_1390_, lean_object* v_args_1391_, lean_object* v_contJpId_1392_, lean_object* v_selfSets_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1389_, v_info_1390_, v_args_1391_, v_contJpId_1392_, v_selfSets_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(lean_object* v_alt_1400_, lean_object* v_f_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___y_1408_; 
switch(lean_obj_tag(v_alt_1400_))
{
case 0:
{
lean_object* v_code_1427_; 
v_code_1427_ = lean_ctor_get(v_alt_1400_, 2);
lean_inc_ref(v_code_1427_);
v___y_1408_ = v_code_1427_;
goto v___jp_1407_;
}
case 1:
{
lean_object* v_code_1428_; 
v_code_1428_ = lean_ctor_get(v_alt_1400_, 1);
lean_inc_ref(v_code_1428_);
v___y_1408_ = v_code_1428_;
goto v___jp_1407_;
}
default: 
{
lean_object* v_code_1429_; 
v_code_1429_ = lean_ctor_get(v_alt_1400_, 0);
lean_inc_ref(v_code_1429_);
v___y_1408_ = v_code_1429_;
goto v___jp_1407_;
}
}
v___jp_1407_:
{
lean_object* v___x_1409_; 
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
v___x_1409_ = lean_apply_6(v_f_1401_, v___y_1408_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, lean_box(0));
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1418_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1418_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1418_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1400_, v_a_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1414_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v_alt_1400_);
v_a_1419_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1409_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1409_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(lean_object* v_alt_1430_, lean_object* v_f_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1430_, v_f_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(uint8_t v_pu_1438_, lean_object* v_alt_1439_, lean_object* v_f_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1439_, v_f_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(lean_object* v_pu_1447_, lean_object* v_alt_1448_, lean_object* v_f_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
uint8_t v_pu_boxed_1455_; lean_object* v_res_1456_; 
v_pu_boxed_1455_ = lean_unbox(v_pu_1447_);
v_res_1456_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(v_pu_boxed_1455_, v_alt_1448_, v_f_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1456_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0(void){
_start:
{
uint8_t v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = 1;
v___x_1458_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v_toApplicative_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1500_; 
v___x_1465_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_1466_ = l_StateRefT_x27_instMonad___redArg(v___x_1465_);
v_toApplicative_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v___x_1466_, 1);
lean_dec(v_unused_1501_);
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1500_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_toApplicative_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1500_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_toFunctor_1471_; lean_object* v_toSeq_1472_; lean_object* v_toSeqLeft_1473_; lean_object* v_toSeqRight_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1498_; 
v_toFunctor_1471_ = lean_ctor_get(v_toApplicative_1467_, 0);
v_toSeq_1472_ = lean_ctor_get(v_toApplicative_1467_, 2);
v_toSeqLeft_1473_ = lean_ctor_get(v_toApplicative_1467_, 3);
v_toSeqRight_1474_ = lean_ctor_get(v_toApplicative_1467_, 4);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_toApplicative_1467_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v_toApplicative_1467_, 1);
lean_dec(v_unused_1499_);
v___x_1476_ = v_toApplicative_1467_;
v_isShared_1477_ = v_isSharedCheck_1498_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_toSeqRight_1474_);
lean_inc(v_toSeqLeft_1473_);
lean_inc(v_toSeq_1472_);
lean_inc(v_toFunctor_1471_);
lean_dec(v_toApplicative_1467_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1498_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___f_1478_; lean_object* v___f_1479_; lean_object* v___f_1480_; lean_object* v___f_1481_; lean_object* v___x_1482_; lean_object* v___f_1483_; lean_object* v___f_1484_; lean_object* v___f_1485_; lean_object* v___x_1487_; 
v___f_1478_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_1479_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1471_);
v___f_1480_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1480_, 0, v_toFunctor_1471_);
v___f_1481_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1481_, 0, v_toFunctor_1471_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___f_1480_);
lean_ctor_set(v___x_1482_, 1, v___f_1481_);
v___f_1483_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1483_, 0, v_toSeqRight_1474_);
v___f_1484_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1484_, 0, v_toSeqLeft_1473_);
v___f_1485_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1485_, 0, v_toSeq_1472_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 4, v___f_1483_);
lean_ctor_set(v___x_1476_, 3, v___f_1484_);
lean_ctor_set(v___x_1476_, 2, v___f_1485_);
lean_ctor_set(v___x_1476_, 1, v___f_1478_);
lean_ctor_set(v___x_1476_, 0, v___x_1482_);
v___x_1487_ = v___x_1476_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___f_1478_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v___f_1485_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v___f_1484_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v___f_1483_);
v___x_1487_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___f_1479_);
lean_ctor_set(v___x_1469_, 0, v___x_1487_);
v___x_1489_ = v___x_1469_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___f_1479_);
v___x_1489_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___f_1493_; lean_object* v___x_6838__overap_1494_; lean_object* v___x_1495_; 
v___x_1490_ = l_StateRefT_x27_instMonad___redArg(v___x_1489_);
v___x_1491_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0);
v___x_1492_ = l_instInhabitedOfMonad___redArg(v___x_1490_, v___x_1491_);
v___f_1493_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1493_, 0, v___x_1492_);
v___x_6838__overap_1494_ = lean_panic_fn_borrowed(v___f_1493_, v_msg_1459_);
lean_dec_ref(v___f_1493_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
v___x_1495_ = lean_apply_5(v___x_6838__overap_1494_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, lean_box(0));
return v___x_1495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object* v_msg_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v_msg_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1508_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_box(0);
v___x_1516_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3));
v___x_1517_ = l_Lean_Expr_const___override(v___x_1516_, v___x_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object* v_resetTokenId_1518_, lean_object* v_origAllocId_1519_, lean_object* v_isSharedId_1520_, lean_object* v_resultType_1521_, lean_object* v_x_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(v_resetTokenId_1518_, v_origAllocId_1519_, v_isSharedId_1520_, v_resultType_1521_, v_x_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object* v_resetTokenId_1529_, lean_object* v_origAllocId_1530_, lean_object* v_isSharedId_1531_, lean_object* v_resultType_1532_, lean_object* v_i_1533_, lean_object* v_as_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1540_ = lean_array_get_size(v_as_1534_);
v___x_1541_ = lean_nat_dec_lt(v_i_1533_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; 
lean_dec(v_i_1533_);
lean_dec_ref(v_resultType_1532_);
lean_dec(v_isSharedId_1531_);
lean_dec(v_origAllocId_1530_);
lean_dec(v_resetTokenId_1529_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_as_1534_);
return v___x_1542_;
}
else
{
lean_object* v___f_1543_; lean_object* v_a_1544_; lean_object* v___x_1545_; 
lean_inc_ref(v_resultType_1532_);
lean_inc(v_isSharedId_1531_);
lean_inc(v_origAllocId_1530_);
lean_inc(v_resetTokenId_1529_);
v___f_1543_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1543_, 0, v_resetTokenId_1529_);
lean_closure_set(v___f_1543_, 1, v_origAllocId_1530_);
lean_closure_set(v___f_1543_, 2, v_isSharedId_1531_);
lean_closure_set(v___f_1543_, 3, v_resultType_1532_);
v_a_1544_ = lean_array_fget_borrowed(v_as_1534_, v_i_1533_);
lean_inc(v_a_1544_);
v___x_1545_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_1544_, v___f_1543_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; size_t v___x_1547_; size_t v___x_1548_; uint8_t v___x_1549_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = lean_ptr_addr(v_a_1544_);
v___x_1548_ = lean_ptr_addr(v_a_1546_);
v___x_1549_ = lean_usize_dec_eq(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_add(v_i_1533_, v___x_1550_);
v___x_1552_ = lean_array_fset(v_as_1534_, v_i_1533_, v_a_1546_);
lean_dec(v_i_1533_);
v_i_1533_ = v___x_1551_;
v_as_1534_ = v___x_1552_;
goto _start;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec(v_a_1546_);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_add(v_i_1533_, v___x_1554_);
lean_dec(v_i_1533_);
v_i_1533_ = v___x_1555_;
goto _start;
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v_as_1534_);
lean_dec(v_i_1533_);
lean_dec_ref(v_resultType_1532_);
lean_dec(v_isSharedId_1531_);
lean_dec(v_origAllocId_1530_);
lean_dec(v_resetTokenId_1529_);
v_a_1557_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1545_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1545_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1567_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6));
v___x_1568_ = lean_unsigned_to_nat(6u);
v___x_1569_ = lean_unsigned_to_nat(208u);
v___x_1570_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5));
v___x_1571_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_1572_ = l_mkPanicMessageWithDecl(v___x_1571_, v___x_1570_, v___x_1569_, v___x_1568_, v___x_1567_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object* v_resetTokenId_1573_, lean_object* v_code_1574_, lean_object* v_origAllocId_1575_, lean_object* v_isSharedId_1576_, lean_object* v_currentRetType_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
switch(lean_obj_tag(v_code_1574_))
{
case 0:
{
lean_object* v_decl_1583_; lean_object* v_value_1584_; 
v_decl_1583_ = lean_ctor_get(v_code_1574_, 0);
v_value_1584_ = lean_ctor_get(v_decl_1583_, 3);
lean_inc(v_value_1584_);
if (lean_obj_tag(v_value_1584_) == 12)
{
lean_object* v_k_1585_; lean_object* v_fvarId_1586_; lean_object* v_binderName_1587_; lean_object* v_type_1588_; lean_object* v_var_1589_; lean_object* v_i_1590_; uint8_t v_updateHeader_1591_; lean_object* v_args_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1708_; 
v_k_1585_ = lean_ctor_get(v_code_1574_, 1);
v_fvarId_1586_ = lean_ctor_get(v_decl_1583_, 0);
v_binderName_1587_ = lean_ctor_get(v_decl_1583_, 1);
v_type_1588_ = lean_ctor_get(v_decl_1583_, 2);
v_var_1589_ = lean_ctor_get(v_value_1584_, 0);
v_i_1590_ = lean_ctor_get(v_value_1584_, 1);
v_updateHeader_1591_ = lean_ctor_get_uint8(v_value_1584_, sizeof(void*)*3);
v_args_1592_ = lean_ctor_get(v_value_1584_, 2);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_value_1584_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1594_ = v_value_1584_;
v_isShared_1595_ = v_isSharedCheck_1708_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_args_1592_);
lean_inc(v_i_1590_);
lean_inc(v_var_1589_);
lean_dec(v_value_1584_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1708_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
uint8_t v___x_1596_; 
v___x_1596_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1573_, v_var_1589_);
lean_dec(v_var_1589_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; 
lean_del_object(v___x_1594_);
lean_dec_ref(v_args_1592_);
lean_dec_ref(v_i_1590_);
lean_inc_ref(v_k_1585_);
v___x_1597_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_k_1585_, v_origAllocId_1575_, v_isSharedId_1576_, v_currentRetType_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1620_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1620_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1620_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
size_t v___x_1602_; size_t v___x_1603_; uint8_t v___x_1604_; 
v___x_1602_ = lean_ptr_addr(v_k_1585_);
v___x_1603_ = lean_ptr_addr(v_a_1598_);
v___x_1604_ = lean_usize_dec_eq(v___x_1602_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1614_; 
lean_inc_ref(v_decl_1583_);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; lean_object* v_unused_1616_; 
v_unused_1615_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1616_);
v___x_1606_ = v_code_1574_;
v_isShared_1607_ = v_isSharedCheck_1614_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v_code_1574_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1614_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 1, v_a_1598_);
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_decl_1583_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_a_1598_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1609_);
v___x_1611_ = v___x_1600_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_object* v___x_1618_; 
lean_dec(v_a_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_code_1574_);
v___x_1618_ = v___x_1600_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_code_1574_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1574_, 2);
return v___x_1597_;
}
}
else
{
lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1705_; 
lean_inc_ref(v_k_1585_);
lean_inc_ref(v_decl_1583_);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; lean_object* v_unused_1707_; 
v_unused_1706_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1707_);
v___x_1622_ = v_code_1574_;
v_isShared_1623_ = v_isSharedCheck_1705_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v_code_1574_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1705_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; 
v___x_1624_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_fvarId_1586_, v_k_1585_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v_fst_1626_; lean_object* v_snd_1627_; lean_object* v___x_1628_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v_fst_1626_ = lean_ctor_get(v_a_1625_, 0);
lean_inc(v_fst_1626_);
v_snd_1627_ = lean_ctor_get(v_a_1625_, 1);
lean_inc(v_snd_1627_);
lean_dec(v_a_1625_);
v___x_1628_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_origAllocId_1575_, v_fst_1626_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_fst_1626_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v_fst_1630_; lean_object* v_snd_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v_fst_1630_ = lean_ctor_get(v_a_1629_, 0);
lean_inc(v_fst_1630_);
v_snd_1631_ = lean_ctor_get(v_a_1629_, 1);
lean_inc(v_snd_1631_);
lean_dec(v_a_1629_);
v___x_1632_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1));
v___x_1633_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1632_, v_a_1579_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; lean_object* v___x_1639_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = 1;
v___x_1636_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1635_, v_snd_1631_, v_snd_1627_);
lean_dec(v_snd_1631_);
v___x_1637_ = 0;
lean_inc_ref(v_type_1588_);
lean_inc(v_binderName_1587_);
lean_inc(v_fvarId_1586_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 0);
lean_ctor_set(v___x_1594_, 2, v_type_1588_);
lean_ctor_set(v___x_1594_, 1, v_binderName_1587_);
lean_ctor_set(v___x_1594_, 0, v_fvarId_1586_);
v___x_1639_ = v___x_1594_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_fvarId_1586_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_binderName_1587_);
lean_ctor_set(v_reuseFailAlloc_1680_, 2, v_type_1588_);
v___x_1639_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3, v___x_1637_);
v___x_1640_ = lean_unsigned_to_nat(1u);
v___x_1641_ = lean_mk_empty_array_with_capacity(v___x_1640_);
v___x_1642_ = lean_array_push(v___x_1641_, v___x_1639_);
lean_inc_ref(v_currentRetType_1577_);
v___x_1643_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_1635_, v_a_1634_, v_currentRetType_1577_, v___x_1642_, v___x_1636_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v_fvarId_1645_; lean_object* v___x_1646_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v_fvarId_1645_ = lean_ctor_get(v_a_1644_, 0);
lean_inc(v_fvarId_1645_);
lean_inc_ref(v_args_1592_);
lean_inc_ref(v_i_1590_);
lean_inc_ref(v_decl_1583_);
v___x_1646_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1583_, v_i_1590_, v_args_1592_, v_fvarId_1645_, v_fst_1630_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
lean_inc(v_fvarId_1645_);
v___x_1648_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1573_, v_i_1590_, v_updateHeader_1591_, v_args_1592_, v_fvarId_1645_, v_origAllocId_1575_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_origAllocId_1575_);
lean_dec_ref(v_args_1592_);
lean_dec_ref(v_i_1590_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_1635_, v_decl_1583_, v_a_1579_);
lean_dec_ref(v_decl_1583_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec_ref_known(v___x_1650_, 1);
v___x_1651_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_1652_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_isSharedId_1576_, v___x_1651_, v_currentRetType_1577_, v_a_1647_, v_a_1649_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1663_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 2);
lean_ctor_set(v___x_1622_, 1, v_a_1653_);
lean_ctor_set(v___x_1622_, 0, v_a_1644_);
v___x_1658_ = v___x_1622_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1644_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1658_);
v___x_1660_ = v___x_1655_;
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
else
{
lean_dec(v_a_1644_);
lean_del_object(v___x_1622_);
return v___x_1652_;
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_a_1649_);
lean_dec(v_a_1647_);
lean_dec(v_a_1644_);
lean_del_object(v___x_1622_);
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
v_a_1664_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1650_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1650_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_dec(v_a_1647_);
lean_dec(v_a_1644_);
lean_del_object(v___x_1622_);
lean_dec_ref(v_decl_1583_);
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
return v___x_1648_;
}
}
else
{
lean_dec(v_a_1644_);
lean_del_object(v___x_1622_);
lean_dec_ref(v_args_1592_);
lean_dec_ref(v_i_1590_);
lean_dec_ref(v_decl_1583_);
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
lean_dec(v_origAllocId_1575_);
lean_dec(v_resetTokenId_1573_);
return v___x_1646_;
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_fst_1630_);
lean_del_object(v___x_1622_);
lean_dec_ref(v_args_1592_);
lean_dec_ref(v_i_1590_);
lean_dec_ref(v_decl_1583_);
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
lean_dec(v_origAllocId_1575_);
lean_dec(v_resetTokenId_1573_);
v_a_1672_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1643_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1643_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_snd_1631_);
lean_dec(v_fst_1630_);
lean_dec(v_snd_1627_);
lean_del_object(v___x_1622_);
lean_del_object(v___x_1594_);
lean_dec_ref(v_args_1592_);
lean_dec_ref(v_i_1590_);
lean_dec_ref(v_decl_1583_);
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
lean_dec(v_origAllocId_1575_);
lean_dec(v_resetTokenId_1573_);
v_a_1681_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1633_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1633_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_snd_1627_);
lean_del_object(v___x_1622_);
lean_del_object(v___x_1594_);
lean_dec_ref(v_args_1592_);
lean_dec_ref(v_i_1590_);
lean_dec_ref(v_decl_1583_);
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
lean_dec(v_origAllocId_1575_);
lean_dec(v_resetTokenId_1573_);
v_a_1689_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1628_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1628_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
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
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_del_object(v___x_1622_);
lean_del_object(v___x_1594_);
lean_dec_ref(v_args_1592_);
lean_dec_ref(v_i_1590_);
lean_dec_ref(v_decl_1583_);
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
lean_dec(v_origAllocId_1575_);
lean_dec(v_resetTokenId_1573_);
v_a_1697_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1624_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1624_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
}
}
else
{
lean_object* v_k_1709_; lean_object* v___x_1710_; 
lean_dec(v_value_1584_);
v_k_1709_ = lean_ctor_get(v_code_1574_, 1);
lean_inc_ref(v_k_1709_);
v___x_1710_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_k_1709_, v_origAllocId_1575_, v_isSharedId_1576_, v_currentRetType_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1733_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1733_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1733_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
size_t v___x_1715_; size_t v___x_1716_; uint8_t v___x_1717_; 
v___x_1715_ = lean_ptr_addr(v_k_1709_);
v___x_1716_ = lean_ptr_addr(v_a_1711_);
v___x_1717_ = lean_usize_dec_eq(v___x_1715_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1727_; 
lean_inc_ref(v_decl_1583_);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; lean_object* v_unused_1729_; 
v_unused_1728_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_1728_);
v_unused_1729_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1729_);
v___x_1719_ = v_code_1574_;
v_isShared_1720_ = v_isSharedCheck_1727_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v_code_1574_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1727_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v_a_1711_);
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_decl_1583_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_a_1711_);
v___x_1722_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1722_);
v___x_1724_ = v___x_1713_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_a_1711_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v_code_1574_);
v___x_1731_ = v___x_1713_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_code_1574_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1574_, 2);
return v___x_1710_;
}
}
}
case 2:
{
lean_object* v_decl_1734_; lean_object* v_k_1735_; lean_object* v_params_1736_; lean_object* v_type_1737_; lean_object* v_value_1738_; lean_object* v___x_1739_; 
v_decl_1734_ = lean_ctor_get(v_code_1574_, 0);
v_k_1735_ = lean_ctor_get(v_code_1574_, 1);
v_params_1736_ = lean_ctor_get(v_decl_1734_, 2);
v_type_1737_ = lean_ctor_get(v_decl_1734_, 3);
v_value_1738_ = lean_ctor_get(v_decl_1734_, 4);
lean_inc_ref(v_type_1737_);
lean_inc(v_isSharedId_1576_);
lean_inc(v_origAllocId_1575_);
lean_inc_ref(v_value_1738_);
lean_inc(v_resetTokenId_1573_);
v___x_1739_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_value_1738_, v_origAllocId_1575_, v_isSharedId_1576_, v_type_1737_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = 1;
lean_inc_ref(v_params_1736_);
lean_inc_ref(v_type_1737_);
lean_inc_ref(v_decl_1734_);
v___x_1742_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1741_, v_decl_1734_, v_type_1737_, v_params_1736_, v_a_1740_, v_a_1579_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
lean_inc_ref(v_k_1735_);
v___x_1744_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_k_1735_, v_origAllocId_1575_, v_isSharedId_1576_, v_currentRetType_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1782_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1782_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1782_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
size_t v___x_1749_; size_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1749_ = lean_ptr_addr(v_k_1735_);
v___x_1750_ = lean_ptr_addr(v_a_1745_);
v___x_1751_ = lean_usize_dec_eq(v___x_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1761_; 
v_isSharedCheck_1761_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; lean_object* v_unused_1763_; 
v_unused_1762_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_1762_);
v_unused_1763_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1763_);
v___x_1753_ = v_code_1574_;
v_isShared_1754_ = v_isSharedCheck_1761_;
goto v_resetjp_1752_;
}
else
{
lean_dec(v_code_1574_);
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
lean_ctor_set(v___x_1753_, 0, v_a_1743_);
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1743_);
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
size_t v___x_1764_; size_t v___x_1765_; uint8_t v___x_1766_; 
v___x_1764_ = lean_ptr_addr(v_decl_1734_);
v___x_1765_ = lean_ptr_addr(v_a_1743_);
v___x_1766_ = lean_usize_dec_eq(v___x_1764_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1776_; 
v_isSharedCheck_1776_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; lean_object* v_unused_1778_; 
v_unused_1777_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1778_);
v___x_1768_ = v_code_1574_;
v_isShared_1769_ = v_isSharedCheck_1776_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v_code_1574_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1776_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v_a_1745_);
lean_ctor_set(v___x_1768_, 0, v_a_1743_);
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1743_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_a_1745_);
v___x_1771_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1773_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1771_);
v___x_1773_ = v___x_1747_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_object* v___x_1780_; 
lean_dec(v_a_1745_);
lean_dec(v_a_1743_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v_code_1574_);
v___x_1780_ = v___x_1747_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_code_1574_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
else
{
lean_dec(v_a_1743_);
lean_dec_ref_known(v_code_1574_, 2);
return v___x_1744_;
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec_ref_known(v_code_1574_, 2);
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
lean_dec(v_origAllocId_1575_);
lean_dec(v_resetTokenId_1573_);
v_a_1783_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1742_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1742_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1574_, 2);
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
lean_dec(v_origAllocId_1575_);
lean_dec(v_resetTokenId_1573_);
return v___x_1739_;
}
}
case 4:
{
lean_object* v_cases_1791_; lean_object* v_typeName_1792_; lean_object* v_resultType_1793_; lean_object* v_discr_1794_; lean_object* v_alts_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1834_; 
lean_dec_ref(v_currentRetType_1577_);
v_cases_1791_ = lean_ctor_get(v_code_1574_, 0);
lean_inc_ref(v_cases_1791_);
v_typeName_1792_ = lean_ctor_get(v_cases_1791_, 0);
v_resultType_1793_ = lean_ctor_get(v_cases_1791_, 1);
v_discr_1794_ = lean_ctor_get(v_cases_1791_, 2);
v_alts_1795_ = lean_ctor_get(v_cases_1791_, 3);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_cases_1791_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1797_ = v_cases_1791_;
v_isShared_1798_ = v_isSharedCheck_1834_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_alts_1795_);
lean_inc(v_discr_1794_);
lean_inc(v_resultType_1793_);
lean_inc(v_typeName_1792_);
lean_dec(v_cases_1791_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1834_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1795_);
lean_inc_ref(v_resultType_1793_);
v___x_1800_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_1573_, v_origAllocId_1575_, v_isSharedId_1576_, v_resultType_1793_, v___x_1799_, v_alts_1795_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1825_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1825_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1825_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
size_t v___x_1805_; size_t v___x_1806_; uint8_t v___x_1807_; 
v___x_1805_ = lean_ptr_addr(v_alts_1795_);
lean_dec_ref(v_alts_1795_);
v___x_1806_ = lean_ptr_addr(v_a_1801_);
v___x_1807_ = lean_usize_dec_eq(v___x_1805_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1820_; 
v_isSharedCheck_1820_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1821_);
v___x_1809_ = v_code_1574_;
v_isShared_1810_ = v_isSharedCheck_1820_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v_code_1574_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1820_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 3, v_a_1801_);
v___x_1812_ = v___x_1797_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_typeName_1792_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_resultType_1793_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_discr_1794_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_a_1801_);
v___x_1812_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1812_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1816_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1814_);
v___x_1816_ = v___x_1803_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
else
{
lean_object* v___x_1823_; 
lean_dec(v_a_1801_);
lean_del_object(v___x_1797_);
lean_dec(v_discr_1794_);
lean_dec_ref(v_resultType_1793_);
lean_dec(v_typeName_1792_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v_code_1574_);
v___x_1823_ = v___x_1803_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_code_1574_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_del_object(v___x_1797_);
lean_dec_ref(v_alts_1795_);
lean_dec(v_discr_1794_);
lean_dec_ref(v_resultType_1793_);
lean_dec(v_typeName_1792_);
lean_dec_ref_known(v_code_1574_, 1);
v_a_1826_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1800_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1800_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1835_; lean_object* v_i_1836_; lean_object* v_y_1837_; lean_object* v_k_1838_; lean_object* v___x_1839_; 
v_fvarId_1835_ = lean_ctor_get(v_code_1574_, 0);
v_i_1836_ = lean_ctor_get(v_code_1574_, 1);
v_y_1837_ = lean_ctor_get(v_code_1574_, 2);
v_k_1838_ = lean_ctor_get(v_code_1574_, 3);
lean_inc_ref(v_k_1838_);
v___x_1839_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_k_1838_, v_origAllocId_1575_, v_isSharedId_1576_, v_currentRetType_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1864_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1864_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1864_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
size_t v___x_1844_; size_t v___x_1845_; uint8_t v___x_1846_; 
v___x_1844_ = lean_ptr_addr(v_k_1838_);
v___x_1845_ = lean_ptr_addr(v_a_1840_);
v___x_1846_ = lean_usize_dec_eq(v___x_1844_, v___x_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1856_; 
lean_inc(v_y_1837_);
lean_inc(v_i_1836_);
lean_inc(v_fvarId_1835_);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; 
v_unused_1857_ = lean_ctor_get(v_code_1574_, 3);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_code_1574_, 2);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1860_);
v___x_1848_ = v_code_1574_;
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
else
{
lean_dec(v_code_1574_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 3, v_a_1840_);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_fvarId_1835_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_i_1836_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v_y_1837_);
lean_ctor_set(v_reuseFailAlloc_1855_, 3, v_a_1840_);
v___x_1851_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1851_);
v___x_1853_ = v___x_1842_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v___x_1862_; 
lean_dec(v_a_1840_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v_code_1574_);
v___x_1862_ = v___x_1842_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_code_1574_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1574_, 4);
return v___x_1839_;
}
}
case 8:
{
lean_object* v_fvarId_1865_; lean_object* v_i_1866_; lean_object* v_y_1867_; lean_object* v_k_1868_; lean_object* v___x_1869_; 
v_fvarId_1865_ = lean_ctor_get(v_code_1574_, 0);
v_i_1866_ = lean_ctor_get(v_code_1574_, 1);
v_y_1867_ = lean_ctor_get(v_code_1574_, 2);
v_k_1868_ = lean_ctor_get(v_code_1574_, 3);
lean_inc_ref(v_k_1868_);
v___x_1869_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_k_1868_, v_origAllocId_1575_, v_isSharedId_1576_, v_currentRetType_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1894_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1894_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1894_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
size_t v___x_1874_; size_t v___x_1875_; uint8_t v___x_1876_; 
v___x_1874_ = lean_ptr_addr(v_k_1868_);
v___x_1875_ = lean_ptr_addr(v_a_1870_);
v___x_1876_ = lean_usize_dec_eq(v___x_1874_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1886_; 
lean_inc(v_y_1867_);
lean_inc(v_i_1866_);
lean_inc(v_fvarId_1865_);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; lean_object* v_unused_1888_; lean_object* v_unused_1889_; lean_object* v_unused_1890_; 
v_unused_1887_ = lean_ctor_get(v_code_1574_, 3);
lean_dec(v_unused_1887_);
v_unused_1888_ = lean_ctor_get(v_code_1574_, 2);
lean_dec(v_unused_1888_);
v_unused_1889_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_1889_);
v_unused_1890_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1890_);
v___x_1878_ = v_code_1574_;
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
else
{
lean_dec(v_code_1574_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 3, v_a_1870_);
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_fvarId_1865_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_i_1866_);
lean_ctor_set(v_reuseFailAlloc_1885_, 2, v_y_1867_);
lean_ctor_set(v_reuseFailAlloc_1885_, 3, v_a_1870_);
v___x_1881_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1883_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1881_);
v___x_1883_ = v___x_1872_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v___x_1892_; 
lean_dec(v_a_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v_code_1574_);
v___x_1892_ = v___x_1872_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_code_1574_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1574_, 4);
return v___x_1869_;
}
}
case 9:
{
lean_object* v_fvarId_1895_; lean_object* v_i_1896_; lean_object* v_offset_1897_; lean_object* v_y_1898_; lean_object* v_ty_1899_; lean_object* v_k_1900_; lean_object* v___x_1901_; 
v_fvarId_1895_ = lean_ctor_get(v_code_1574_, 0);
v_i_1896_ = lean_ctor_get(v_code_1574_, 1);
v_offset_1897_ = lean_ctor_get(v_code_1574_, 2);
v_y_1898_ = lean_ctor_get(v_code_1574_, 3);
v_ty_1899_ = lean_ctor_get(v_code_1574_, 4);
v_k_1900_ = lean_ctor_get(v_code_1574_, 5);
lean_inc_ref(v_k_1900_);
v___x_1901_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_k_1900_, v_origAllocId_1575_, v_isSharedId_1576_, v_currentRetType_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1928_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1928_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1928_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
size_t v___x_1906_; size_t v___x_1907_; uint8_t v___x_1908_; 
v___x_1906_ = lean_ptr_addr(v_k_1900_);
v___x_1907_ = lean_ptr_addr(v_a_1902_);
v___x_1908_ = lean_usize_dec_eq(v___x_1906_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1918_; 
lean_inc_ref(v_ty_1899_);
lean_inc(v_y_1898_);
lean_inc(v_offset_1897_);
lean_inc(v_i_1896_);
lean_inc(v_fvarId_1895_);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; lean_object* v_unused_1920_; lean_object* v_unused_1921_; lean_object* v_unused_1922_; lean_object* v_unused_1923_; lean_object* v_unused_1924_; 
v_unused_1919_ = lean_ctor_get(v_code_1574_, 5);
lean_dec(v_unused_1919_);
v_unused_1920_ = lean_ctor_get(v_code_1574_, 4);
lean_dec(v_unused_1920_);
v_unused_1921_ = lean_ctor_get(v_code_1574_, 3);
lean_dec(v_unused_1921_);
v_unused_1922_ = lean_ctor_get(v_code_1574_, 2);
lean_dec(v_unused_1922_);
v_unused_1923_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1924_);
v___x_1910_ = v_code_1574_;
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
else
{
lean_dec(v_code_1574_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 5, v_a_1902_);
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_fvarId_1895_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_i_1896_);
lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_offset_1897_);
lean_ctor_set(v_reuseFailAlloc_1917_, 3, v_y_1898_);
lean_ctor_set(v_reuseFailAlloc_1917_, 4, v_ty_1899_);
lean_ctor_set(v_reuseFailAlloc_1917_, 5, v_a_1902_);
v___x_1913_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1915_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1913_);
v___x_1915_ = v___x_1904_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v___x_1926_; 
lean_dec(v_a_1902_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v_code_1574_);
v___x_1926_ = v___x_1904_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_code_1574_);
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
lean_dec_ref_known(v_code_1574_, 6);
return v___x_1901_;
}
}
case 10:
{
lean_object* v_fvarId_1929_; lean_object* v_cidx_1930_; lean_object* v_k_1931_; lean_object* v___x_1932_; 
v_fvarId_1929_ = lean_ctor_get(v_code_1574_, 0);
v_cidx_1930_ = lean_ctor_get(v_code_1574_, 1);
v_k_1931_ = lean_ctor_get(v_code_1574_, 2);
lean_inc_ref(v_k_1931_);
v___x_1932_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_k_1931_, v_origAllocId_1575_, v_isSharedId_1576_, v_currentRetType_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1956_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1956_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1956_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
size_t v___x_1937_; size_t v___x_1938_; uint8_t v___x_1939_; 
v___x_1937_ = lean_ptr_addr(v_k_1931_);
v___x_1938_ = lean_ptr_addr(v_a_1933_);
v___x_1939_ = lean_usize_dec_eq(v___x_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1949_; 
lean_inc(v_cidx_1930_);
lean_inc(v_fvarId_1929_);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; lean_object* v_unused_1951_; lean_object* v_unused_1952_; 
v_unused_1950_ = lean_ctor_get(v_code_1574_, 2);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1952_);
v___x_1941_ = v_code_1574_;
v_isShared_1942_ = v_isSharedCheck_1949_;
goto v_resetjp_1940_;
}
else
{
lean_dec(v_code_1574_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1949_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 2, v_a_1933_);
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_fvarId_1929_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_cidx_1930_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_a_1933_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1944_);
v___x_1946_ = v___x_1935_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_1954_; 
lean_dec(v_a_1933_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v_code_1574_);
v___x_1954_ = v___x_1935_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_code_1574_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1574_, 3);
return v___x_1932_;
}
}
case 11:
{
lean_object* v_fvarId_1957_; lean_object* v_n_1958_; uint8_t v_check_1959_; uint8_t v_persistent_1960_; lean_object* v_k_1961_; lean_object* v___x_1962_; 
v_fvarId_1957_ = lean_ctor_get(v_code_1574_, 0);
v_n_1958_ = lean_ctor_get(v_code_1574_, 1);
v_check_1959_ = lean_ctor_get_uint8(v_code_1574_, sizeof(void*)*3);
v_persistent_1960_ = lean_ctor_get_uint8(v_code_1574_, sizeof(void*)*3 + 1);
v_k_1961_ = lean_ctor_get(v_code_1574_, 2);
lean_inc_ref(v_k_1961_);
v___x_1962_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_k_1961_, v_origAllocId_1575_, v_isSharedId_1576_, v_currentRetType_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1986_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1986_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1986_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
size_t v___x_1967_; size_t v___x_1968_; uint8_t v___x_1969_; 
v___x_1967_ = lean_ptr_addr(v_k_1961_);
v___x_1968_ = lean_ptr_addr(v_a_1963_);
v___x_1969_ = lean_usize_dec_eq(v___x_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1979_; 
lean_inc(v_n_1958_);
lean_inc(v_fvarId_1957_);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; lean_object* v_unused_1981_; lean_object* v_unused_1982_; 
v_unused_1980_ = lean_ctor_get(v_code_1574_, 2);
lean_dec(v_unused_1980_);
v_unused_1981_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_1981_);
v_unused_1982_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_1982_);
v___x_1971_ = v_code_1574_;
v_isShared_1972_ = v_isSharedCheck_1979_;
goto v_resetjp_1970_;
}
else
{
lean_dec(v_code_1574_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1979_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 2, v_a_1963_);
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_fvarId_1957_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_n_1958_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_a_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*3, v_check_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*3 + 1, v_persistent_1960_);
v___x_1974_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1976_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1974_);
v___x_1976_ = v___x_1965_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
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
else
{
lean_object* v___x_1984_; 
lean_dec(v_a_1963_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v_code_1574_);
v___x_1984_ = v___x_1965_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_code_1574_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1574_, 3);
return v___x_1962_;
}
}
case 12:
{
lean_object* v_fvarId_1987_; lean_object* v_n_1988_; uint8_t v_check_1989_; uint8_t v_persistent_1990_; lean_object* v_objs_x3f_1991_; lean_object* v_k_1992_; uint8_t v___x_1993_; 
v_fvarId_1987_ = lean_ctor_get(v_code_1574_, 0);
v_n_1988_ = lean_ctor_get(v_code_1574_, 1);
v_check_1989_ = lean_ctor_get_uint8(v_code_1574_, sizeof(void*)*4);
v_persistent_1990_ = lean_ctor_get_uint8(v_code_1574_, sizeof(void*)*4 + 1);
v_objs_x3f_1991_ = lean_ctor_get(v_code_1574_, 2);
v_k_1992_ = lean_ctor_get(v_code_1574_, 3);
v___x_1993_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1573_, v_fvarId_1987_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; 
lean_inc_ref(v_k_1992_);
v___x_1994_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_k_1992_, v_origAllocId_1575_, v_isSharedId_1576_, v_currentRetType_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2019_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2019_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2019_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
size_t v___x_1999_; size_t v___x_2000_; uint8_t v___x_2001_; 
v___x_1999_ = lean_ptr_addr(v_k_1992_);
v___x_2000_ = lean_ptr_addr(v_a_1995_);
v___x_2001_ = lean_usize_dec_eq(v___x_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2011_; 
lean_inc(v_objs_x3f_1991_);
lean_inc(v_n_1988_);
lean_inc(v_fvarId_1987_);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; lean_object* v_unused_2013_; lean_object* v_unused_2014_; lean_object* v_unused_2015_; 
v_unused_2012_ = lean_ctor_get(v_code_1574_, 3);
lean_dec(v_unused_2012_);
v_unused_2013_ = lean_ctor_get(v_code_1574_, 2);
lean_dec(v_unused_2013_);
v_unused_2014_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_2014_);
v_unused_2015_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_2015_);
v___x_2003_ = v_code_1574_;
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v_code_1574_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 3, v_a_1995_);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_fvarId_1987_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_n_1988_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_objs_x3f_1991_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_a_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*4, v_check_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*4 + 1, v_persistent_1990_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2006_);
v___x_2008_ = v___x_1997_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v___x_2017_; 
lean_dec(v_a_1995_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v_code_1574_);
v___x_2017_ = v___x_1997_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_code_1574_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1574_, 4);
return v___x_1994_;
}
}
else
{
lean_object* v___x_2020_; uint8_t v___x_2021_; 
lean_inc_ref(v_k_1992_);
lean_inc(v_n_1988_);
lean_dec_ref_known(v_code_1574_, 4);
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
lean_dec(v_origAllocId_1575_);
v___x_2020_ = lean_unsigned_to_nat(1u);
v___x_2021_ = lean_nat_dec_eq(v_n_1988_, v___x_2020_);
lean_dec(v_n_1988_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec_ref(v_k_1992_);
lean_dec(v_resetTokenId_1573_);
v___x_2022_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7);
v___x_2023_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v___x_2022_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_2024_, 0, v_resetTokenId_1573_);
lean_ctor_set(v___x_2024_, 1, v_k_1992_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
}
}
case 13:
{
lean_object* v_fvarId_2026_; lean_object* v_k_2027_; lean_object* v___x_2028_; 
v_fvarId_2026_ = lean_ctor_get(v_code_1574_, 0);
v_k_2027_ = lean_ctor_get(v_code_1574_, 1);
lean_inc_ref(v_k_2027_);
v___x_2028_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1573_, v_k_2027_, v_origAllocId_1575_, v_isSharedId_1576_, v_currentRetType_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2051_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2051_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2051_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
size_t v___x_2033_; size_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = lean_ptr_addr(v_k_2027_);
v___x_2034_ = lean_ptr_addr(v_a_2029_);
v___x_2035_ = lean_usize_dec_eq(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2045_; 
lean_inc(v_fvarId_2026_);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_code_1574_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; lean_object* v_unused_2047_; 
v_unused_2046_ = lean_ctor_get(v_code_1574_, 1);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_code_1574_, 0);
lean_dec(v_unused_2047_);
v___x_2037_ = v_code_1574_;
v_isShared_2038_ = v_isSharedCheck_2045_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v_code_1574_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2045_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v_a_2029_);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_fvarId_2026_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_a_2029_);
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
lean_object* v___x_2049_; 
lean_dec(v_a_2029_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v_code_1574_);
v___x_2049_ = v___x_2031_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_code_1574_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1574_, 2);
return v___x_2028_;
}
}
default: 
{
lean_object* v___x_2052_; 
lean_dec_ref(v_currentRetType_1577_);
lean_dec(v_isSharedId_1576_);
lean_dec(v_origAllocId_1575_);
lean_dec(v_resetTokenId_1573_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_code_1574_);
return v___x_2052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object* v_resetTokenId_2053_, lean_object* v_origAllocId_2054_, lean_object* v_isSharedId_2055_, lean_object* v_resultType_2056_, lean_object* v_x_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2053_, v_x_2057_, v_origAllocId_2054_, v_isSharedId_2055_, v_resultType_2056_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object* v_resetTokenId_2064_, lean_object* v_origAllocId_2065_, lean_object* v_isSharedId_2066_, lean_object* v_resultType_2067_, lean_object* v_i_2068_, lean_object* v_as_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_2064_, v_origAllocId_2065_, v_isSharedId_2066_, v_resultType_2067_, v_i_2068_, v_as_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object* v_resetTokenId_2076_, lean_object* v_code_2077_, lean_object* v_origAllocId_2078_, lean_object* v_isSharedId_2079_, lean_object* v_currentRetType_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2076_, v_code_2077_, v_origAllocId_2078_, v_isSharedId_2079_, v_currentRetType_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object* v_currentRetType_2096_, lean_object* v_ds_2097_, lean_object* v_decl_2098_, lean_object* v_nFields_2099_, lean_object* v_origAllocId_2100_, lean_object* v_k_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_2099_, v_origAllocId_2100_, v_ds_2097_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2231_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v_fst_2109_ = lean_ctor_get(v_a_2108_, 0);
v_snd_2110_ = lean_ctor_get(v_a_2108_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_a_2108_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2112_ = v_a_2108_;
v_isShared_2113_ = v_isSharedCheck_2231_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snd_2110_);
lean_inc(v_fst_2109_);
lean_dec(v_a_2108_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2231_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1));
v___x_2115_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2114_, v_a_2103_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; lean_object* v___x_2120_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
v___x_2117_ = 1;
v___x_2118_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_2119_ = 0;
v___x_2120_ = l_Lean_Compiler_LCNF_mkParam(v___x_2117_, v_a_2116_, v___x_2118_, v___x_2119_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v_fvarId_2122_; lean_object* v_binderName_2123_; lean_object* v_fvarId_2124_; lean_object* v___x_2125_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v_fvarId_2122_ = lean_ctor_get(v_decl_2098_, 0);
v_binderName_2123_ = lean_ctor_get(v_decl_2098_, 1);
v_fvarId_2124_ = lean_ctor_get(v_a_2121_, 0);
lean_inc_ref(v_currentRetType_2096_);
lean_inc(v_fvarId_2124_);
lean_inc(v_origAllocId_2100_);
lean_inc(v_fvarId_2122_);
v___x_2125_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_fvarId_2122_, v_k_2101_, v_origAllocId_2100_, v_fvarId_2124_, v_currentRetType_2096_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2127_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_currentRetType_2096_);
v___x_2128_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_a_2126_, v___x_2127_, v_currentRetType_2096_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2214_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2214_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2214_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3));
v___x_2134_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2133_, v_a_2103_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_binderName_2123_);
lean_inc(v_fvarId_2122_);
v___x_2137_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2137_, 0, v_fvarId_2122_);
lean_ctor_set(v___x_2137_, 1, v_binderName_2123_);
lean_ctor_set(v___x_2137_, 2, v___x_2136_);
lean_ctor_set_uint8(v___x_2137_, sizeof(void*)*3, v___x_2119_);
v___x_2138_ = lean_unsigned_to_nat(2u);
v___x_2139_ = lean_mk_empty_array_with_capacity(v___x_2138_);
v___x_2140_ = lean_array_push(v___x_2139_, v___x_2137_);
v___x_2141_ = lean_array_push(v___x_2140_, v_a_2121_);
lean_inc_ref(v_currentRetType_2096_);
v___x_2142_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_2117_, v_a_2135_, v_currentRetType_2096_, v___x_2141_, v_a_2129_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5));
v___x_2145_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2144_, v_a_2103_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
lean_inc(v_origAllocId_2100_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 15);
lean_ctor_set(v___x_2131_, 0, v_origAllocId_2100_);
v___x_2148_ = v___x_2131_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_origAllocId_2100_);
v___x_2148_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2117_, v_a_2146_, v___x_2118_, v___x_2148_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v_fvarId_2151_; lean_object* v_fvarId_2152_; lean_object* v___x_2153_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v_fvarId_2151_ = lean_ctor_get(v_a_2143_, 0);
v_fvarId_2152_ = lean_ctor_get(v_a_2150_, 0);
lean_inc(v_fvarId_2152_);
lean_inc(v_fvarId_2151_);
lean_inc(v_origAllocId_2100_);
v___x_2153_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_2100_, v_snd_2110_, v_fvarId_2151_, v_fvarId_2152_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
lean_inc(v_fvarId_2152_);
lean_inc(v_fvarId_2151_);
v___x_2155_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_2100_, v_snd_2110_, v_fvarId_2151_, v_fvarId_2152_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
lean_dec(v_snd_2110_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
lean_inc(v_fvarId_2152_);
v___x_2157_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_fvarId_2152_, v___x_2118_, v_currentRetType_2096_, v_a_2154_, v_a_2156_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2159_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2159_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2117_, v_decl_2098_, v_a_2103_);
lean_dec_ref(v_decl_2098_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2171_; 
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; 
v_unused_2172_ = lean_ctor_get(v___x_2159_, 0);
lean_dec(v_unused_2172_);
v___x_2161_ = v___x_2159_;
v_isShared_2162_ = v_isSharedCheck_2171_;
goto v_resetjp_2160_;
}
else
{
lean_dec(v___x_2159_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2171_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v_a_2158_);
lean_ctor_set(v___x_2112_, 0, v_a_2150_);
v___x_2164_ = v___x_2112_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2150_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_a_2158_);
v___x_2164_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_a_2143_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2117_, v_fst_2109_, v___x_2165_);
lean_dec(v_fst_2109_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2166_);
v___x_2168_ = v___x_2161_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2158_);
lean_dec(v_a_2150_);
lean_dec(v_a_2143_);
lean_del_object(v___x_2112_);
lean_dec(v_fst_2109_);
v_a_2173_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2159_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2159_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_dec(v_a_2150_);
lean_dec(v_a_2143_);
lean_del_object(v___x_2112_);
lean_dec(v_fst_2109_);
lean_dec_ref(v_decl_2098_);
return v___x_2157_;
}
}
else
{
lean_dec(v_a_2154_);
lean_dec(v_a_2150_);
lean_dec(v_a_2143_);
lean_del_object(v___x_2112_);
lean_dec(v_fst_2109_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
return v___x_2155_;
}
}
else
{
lean_dec(v_a_2150_);
lean_dec(v_a_2143_);
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec(v_origAllocId_2100_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
return v___x_2153_;
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v_a_2143_);
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec(v_origAllocId_2100_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
v_a_2181_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2149_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2149_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_a_2143_);
lean_del_object(v___x_2131_);
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec(v_origAllocId_2100_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
v_a_2190_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2145_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2145_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_del_object(v___x_2131_);
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec(v_origAllocId_2100_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
v_a_2198_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2142_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2142_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
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
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2131_);
lean_dec(v_a_2129_);
lean_dec(v_a_2121_);
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec(v_origAllocId_2100_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
v_a_2206_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2134_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2134_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
else
{
lean_dec(v_a_2121_);
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec(v_origAllocId_2100_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
return v___x_2128_;
}
}
else
{
lean_dec(v_a_2121_);
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec(v_origAllocId_2100_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
return v___x_2125_;
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec_ref(v_k_2101_);
lean_dec(v_origAllocId_2100_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
v_a_2215_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2120_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2120_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec_ref(v_k_2101_);
lean_dec(v_origAllocId_2100_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
v_a_2223_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2115_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2115_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_k_2101_);
lean_dec(v_origAllocId_2100_);
lean_dec_ref(v_decl_2098_);
lean_dec_ref(v_currentRetType_2096_);
v_a_2232_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2107_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2107_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object* v_resultType_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(v_resultType_2240_, v_x_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object* v_resultType_2248_, lean_object* v_i_2249_, lean_object* v_as_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2256_ = lean_array_get_size(v_as_2250_);
v___x_2257_ = lean_nat_dec_lt(v_i_2249_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; 
lean_dec(v_i_2249_);
lean_dec_ref(v_resultType_2248_);
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v_as_2250_);
return v___x_2258_;
}
else
{
lean_object* v___f_2259_; lean_object* v_a_2260_; lean_object* v___x_2261_; 
lean_inc_ref(v_resultType_2248_);
v___f_2259_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2259_, 0, v_resultType_2248_);
v_a_2260_ = lean_array_fget_borrowed(v_as_2250_, v_i_2249_);
lean_inc(v_a_2260_);
v___x_2261_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_2260_, v___f_2259_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; size_t v___x_2263_; size_t v___x_2264_; uint8_t v___x_2265_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
v___x_2263_ = lean_ptr_addr(v_a_2260_);
v___x_2264_ = lean_ptr_addr(v_a_2262_);
v___x_2265_ = lean_usize_dec_eq(v___x_2263_, v___x_2264_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = lean_unsigned_to_nat(1u);
v___x_2267_ = lean_nat_add(v_i_2249_, v___x_2266_);
v___x_2268_ = lean_array_fset(v_as_2250_, v_i_2249_, v_a_2262_);
lean_dec(v_i_2249_);
v_i_2249_ = v___x_2267_;
v_as_2250_ = v___x_2268_;
goto _start;
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_a_2262_);
v___x_2270_ = lean_unsigned_to_nat(1u);
v___x_2271_ = lean_nat_add(v_i_2249_, v___x_2270_);
lean_dec(v_i_2249_);
v_i_2249_ = v___x_2271_;
goto _start;
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_as_2250_);
lean_dec(v_i_2249_);
lean_dec_ref(v_resultType_2248_);
v_a_2273_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2261_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2261_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object* v_code_2281_, lean_object* v_ds_2282_, lean_object* v_currentRetType_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_code_2290_; lean_object* v_ds_2291_; lean_object* v_k_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; 
switch(lean_obj_tag(v_code_2281_))
{
case 0:
{
lean_object* v_decl_2301_; lean_object* v_value_2302_; 
v_decl_2301_ = lean_ctor_get(v_code_2281_, 0);
v_value_2302_ = lean_ctor_get(v_decl_2301_, 3);
if (lean_obj_tag(v_value_2302_) == 11)
{
lean_object* v_k_2303_; lean_object* v_n_2304_; lean_object* v_var_2305_; lean_object* v___x_2306_; 
lean_inc_ref(v_decl_2301_);
v_k_2303_ = lean_ctor_get(v_code_2281_, 1);
lean_inc_ref(v_k_2303_);
lean_dec_ref_known(v_code_2281_, 2);
v_n_2304_ = lean_ctor_get(v_value_2302_, 0);
lean_inc(v_n_2304_);
v_var_2305_ = lean_ctor_get(v_value_2302_, 1);
lean_inc(v_var_2305_);
v___x_2306_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2283_, v_ds_2282_, v_decl_2301_, v_n_2304_, v_var_2305_, v_k_2303_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2306_;
}
else
{
lean_object* v_k_2307_; 
v_k_2307_ = lean_ctor_get(v_code_2281_, 1);
lean_inc_ref(v_k_2307_);
v_code_2290_ = v_code_2281_;
v_ds_2291_ = v_ds_2282_;
v_k_2292_ = v_k_2307_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
v___y_2295_ = v_a_2286_;
v___y_2296_ = v_a_2287_;
goto v___jp_2289_;
}
}
case 2:
{
lean_object* v_decl_2308_; lean_object* v_k_2309_; lean_object* v_params_2310_; lean_object* v_type_2311_; lean_object* v_value_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_decl_2308_ = lean_ctor_get(v_code_2281_, 0);
lean_inc_ref(v_decl_2308_);
v_k_2309_ = lean_ctor_get(v_code_2281_, 1);
lean_inc_ref(v_k_2309_);
lean_dec_ref_known(v_code_2281_, 2);
v_params_2310_ = lean_ctor_get(v_decl_2308_, 2);
lean_inc_ref(v_params_2310_);
v_type_2311_ = lean_ctor_get(v_decl_2308_, 3);
lean_inc_ref_n(v_type_2311_, 2);
v_value_2312_ = lean_ctor_get(v_decl_2308_, 4);
v___x_2313_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_value_2312_);
v___x_2314_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_value_2312_, v___x_2313_, v_type_2311_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2335_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2335_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2335_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
uint8_t v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = 1;
v___x_2320_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2319_, v_decl_2308_, v_type_2311_, v_params_2310_, v_a_2315_, v_a_2285_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2323_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
if (v_isShared_2318_ == 0)
{
lean_ctor_set_tag(v___x_2317_, 2);
lean_ctor_set(v___x_2317_, 0, v_a_2321_);
v___x_2323_ = v___x_2317_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2321_);
v___x_2323_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_array_push(v_ds_2282_, v___x_2323_);
v_code_2281_ = v_k_2309_;
v_ds_2282_ = v___x_2324_;
goto _start;
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_del_object(v___x_2317_);
lean_dec_ref(v_k_2309_);
lean_dec_ref(v_currentRetType_2283_);
lean_dec_ref(v_ds_2282_);
v_a_2327_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2320_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2320_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_2311_);
lean_dec_ref(v_params_2310_);
lean_dec_ref(v_k_2309_);
lean_dec_ref(v_decl_2308_);
lean_dec_ref(v_currentRetType_2283_);
lean_dec_ref(v_ds_2282_);
return v___x_2314_;
}
}
case 4:
{
lean_object* v_cases_2336_; lean_object* v_typeName_2337_; lean_object* v_resultType_2338_; lean_object* v_discr_2339_; lean_object* v_alts_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref(v_currentRetType_2283_);
v_cases_2336_ = lean_ctor_get(v_code_2281_, 0);
lean_inc_ref(v_cases_2336_);
v_typeName_2337_ = lean_ctor_get(v_cases_2336_, 0);
v_resultType_2338_ = lean_ctor_get(v_cases_2336_, 1);
v_discr_2339_ = lean_ctor_get(v_cases_2336_, 2);
v_alts_2340_ = lean_ctor_get(v_cases_2336_, 3);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_cases_2336_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2342_ = v_cases_2336_;
v_isShared_2343_ = v_isSharedCheck_2380_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_alts_2340_);
lean_inc(v_discr_2339_);
lean_inc(v_resultType_2338_);
lean_inc(v_typeName_2337_);
lean_dec(v_cases_2336_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2380_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2340_);
lean_inc_ref(v_resultType_2338_);
v___x_2345_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2338_, v___x_2344_, v_alts_2340_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2371_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2371_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2371_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
uint8_t v___x_2350_; lean_object* v___y_2352_; size_t v___x_2357_; size_t v___x_2358_; uint8_t v___x_2359_; 
v___x_2350_ = 1;
v___x_2357_ = lean_ptr_addr(v_alts_2340_);
lean_dec_ref(v_alts_2340_);
v___x_2358_ = lean_ptr_addr(v_a_2346_);
v___x_2359_ = lean_usize_dec_eq(v___x_2357_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2369_; 
v_isSharedCheck_2369_ = !lean_is_exclusive(v_code_2281_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; 
v_unused_2370_ = lean_ctor_get(v_code_2281_, 0);
lean_dec(v_unused_2370_);
v___x_2361_ = v_code_2281_;
v_isShared_2362_ = v_isSharedCheck_2369_;
goto v_resetjp_2360_;
}
else
{
lean_dec(v_code_2281_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2369_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 3, v_a_2346_);
v___x_2364_ = v___x_2342_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_typeName_2337_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_resultType_2338_);
lean_ctor_set(v_reuseFailAlloc_2368_, 2, v_discr_2339_);
lean_ctor_set(v_reuseFailAlloc_2368_, 3, v_a_2346_);
v___x_2364_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2366_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2364_);
v___x_2366_ = v___x_2361_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
v___y_2352_ = v___x_2366_;
goto v___jp_2351_;
}
}
}
}
else
{
lean_dec(v_a_2346_);
lean_del_object(v___x_2342_);
lean_dec(v_discr_2339_);
lean_dec_ref(v_resultType_2338_);
lean_dec(v_typeName_2337_);
v___y_2352_ = v_code_2281_;
goto v___jp_2351_;
}
v___jp_2351_:
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2353_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2350_, v_ds_2282_, v___y_2352_);
lean_dec_ref(v_ds_2282_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2353_);
v___x_2355_ = v___x_2348_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_del_object(v___x_2342_);
lean_dec_ref(v_alts_2340_);
lean_dec(v_discr_2339_);
lean_dec_ref(v_resultType_2338_);
lean_dec(v_typeName_2337_);
lean_dec_ref_known(v_code_2281_, 1);
lean_dec_ref(v_ds_2282_);
v_a_2372_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2345_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2345_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
case 7:
{
lean_object* v_k_2381_; 
v_k_2381_ = lean_ctor_get(v_code_2281_, 3);
lean_inc_ref(v_k_2381_);
v_code_2290_ = v_code_2281_;
v_ds_2291_ = v_ds_2282_;
v_k_2292_ = v_k_2381_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
v___y_2295_ = v_a_2286_;
v___y_2296_ = v_a_2287_;
goto v___jp_2289_;
}
case 8:
{
lean_object* v_k_2382_; 
v_k_2382_ = lean_ctor_get(v_code_2281_, 3);
lean_inc_ref(v_k_2382_);
v_code_2290_ = v_code_2281_;
v_ds_2291_ = v_ds_2282_;
v_k_2292_ = v_k_2382_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
v___y_2295_ = v_a_2286_;
v___y_2296_ = v_a_2287_;
goto v___jp_2289_;
}
case 9:
{
lean_object* v_k_2383_; 
v_k_2383_ = lean_ctor_get(v_code_2281_, 5);
lean_inc_ref(v_k_2383_);
v_code_2290_ = v_code_2281_;
v_ds_2291_ = v_ds_2282_;
v_k_2292_ = v_k_2383_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
v___y_2295_ = v_a_2286_;
v___y_2296_ = v_a_2287_;
goto v___jp_2289_;
}
case 10:
{
lean_object* v_k_2384_; 
v_k_2384_ = lean_ctor_get(v_code_2281_, 2);
lean_inc_ref(v_k_2384_);
v_code_2290_ = v_code_2281_;
v_ds_2291_ = v_ds_2282_;
v_k_2292_ = v_k_2384_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
v___y_2295_ = v_a_2286_;
v___y_2296_ = v_a_2287_;
goto v___jp_2289_;
}
case 11:
{
lean_object* v_k_2385_; 
v_k_2385_ = lean_ctor_get(v_code_2281_, 2);
lean_inc_ref(v_k_2385_);
v_code_2290_ = v_code_2281_;
v_ds_2291_ = v_ds_2282_;
v_k_2292_ = v_k_2385_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
v___y_2295_ = v_a_2286_;
v___y_2296_ = v_a_2287_;
goto v___jp_2289_;
}
case 12:
{
lean_object* v_k_2386_; 
v_k_2386_ = lean_ctor_get(v_code_2281_, 3);
lean_inc_ref(v_k_2386_);
v_code_2290_ = v_code_2281_;
v_ds_2291_ = v_ds_2282_;
v_k_2292_ = v_k_2386_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
v___y_2295_ = v_a_2286_;
v___y_2296_ = v_a_2287_;
goto v___jp_2289_;
}
case 13:
{
lean_object* v_k_2387_; 
v_k_2387_ = lean_ctor_get(v_code_2281_, 1);
lean_inc_ref(v_k_2387_);
v_code_2290_ = v_code_2281_;
v_ds_2291_ = v_ds_2282_;
v_k_2292_ = v_k_2387_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
v___y_2295_ = v_a_2286_;
v___y_2296_ = v_a_2287_;
goto v___jp_2289_;
}
default: 
{
uint8_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_dec_ref(v_currentRetType_2283_);
v___x_2388_ = 1;
v___x_2389_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2388_, v_ds_2282_, v_code_2281_);
lean_dec_ref(v_ds_2282_);
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
return v___x_2390_;
}
}
v___jp_2289_:
{
uint8_t v___x_2297_; lean_object* v_d_2298_; lean_object* v___x_2299_; 
v___x_2297_ = 1;
v_d_2298_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_2297_, v_code_2290_);
lean_dec_ref(v_code_2290_);
v___x_2299_ = lean_array_push(v_ds_2291_, v_d_2298_);
v_code_2281_ = v_k_2292_;
v_ds_2282_ = v___x_2299_;
v_a_2284_ = v___y_2293_;
v_a_2285_ = v___y_2294_;
v_a_2286_ = v___y_2295_;
v_a_2287_ = v___y_2296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object* v_resultType_2391_, lean_object* v_x_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2399_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2392_, v___x_2398_, v_resultType_2391_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object* v_resultType_2400_, lean_object* v_i_2401_, lean_object* v_as_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2400_, v_i_2401_, v_as_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object* v_code_2409_, lean_object* v_ds_2410_, lean_object* v_currentRetType_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_code_2409_, v_ds_2410_, v_currentRetType_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object* v_currentRetType_2418_, lean_object* v_ds_2419_, lean_object* v_decl_2420_, lean_object* v_nFields_2421_, lean_object* v_origAllocId_2422_, lean_object* v_k_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2418_, v_ds_2419_, v_decl_2420_, v_nFields_2421_, v_origAllocId_2422_, v_k_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object* v_f_2430_, lean_object* v_v_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
if (lean_obj_tag(v_v_2431_) == 0)
{
lean_object* v_code_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2461_; 
v_code_2437_ = lean_ctor_get(v_v_2431_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_v_2431_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2439_ = v_v_2431_;
v_isShared_2440_ = v_isSharedCheck_2461_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_code_2437_);
lean_dec(v_v_2431_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2461_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; 
lean_inc(v___y_2435_);
lean_inc_ref(v___y_2434_);
lean_inc(v___y_2433_);
lean_inc_ref(v___y_2432_);
v___x_2441_ = lean_apply_6(v_f_2430_, v_code_2437_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, lean_box(0));
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2452_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2444_ = v___x_2441_;
v_isShared_2445_ = v_isSharedCheck_2452_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2441_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2452_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_a_2442_);
v___x_2447_ = v___x_2439_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2449_; 
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2447_);
v___x_2449_ = v___x_2444_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_del_object(v___x_2439_);
v_a_2453_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2441_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2441_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
else
{
lean_object* v___x_2462_; 
lean_dec_ref(v_f_2430_);
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v_v_2431_);
return v___x_2462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object* v_f_2463_, lean_object* v_v_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2463_, v_v_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t v_pu_2471_, lean_object* v_f_2472_, lean_object* v_v_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2472_, v_v_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object* v_pu_2480_, lean_object* v_f_2481_, lean_object* v_v_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
uint8_t v_pu_boxed_2488_; lean_object* v_res_2489_; 
v_pu_boxed_2488_ = lean_unbox(v_pu_2480_);
v_res_2489_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(v_pu_boxed_2488_, v_f_2481_, v_v_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object* v_toSignature_2490_, lean_object* v_x_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_type_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_type_2497_ = lean_ctor_get(v_toSignature_2490_, 2);
lean_inc_ref(v_type_2497_);
lean_dec_ref(v_toSignature_2490_);
v___x_2498_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2499_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2491_, v___x_2498_, v_type_2497_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object* v_toSignature_2500_, lean_object* v_x_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(v_toSignature_2500_, v_x_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object* v_decl_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2509_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2552_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2552_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2552_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
uint8_t v_resetReuse_2519_; 
v_resetReuse_2519_ = lean_ctor_get_uint8(v_a_2515_, sizeof(void*)*4 + 2);
lean_dec(v_a_2515_);
if (v_resetReuse_2519_ == 0)
{
lean_object* v___x_2521_; 
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v_decl_2508_);
v___x_2521_ = v___x_2517_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_decl_2508_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
else
{
lean_object* v_toSignature_2523_; lean_object* v_value_2524_; uint8_t v_recursive_2525_; lean_object* v_inlineAttr_x3f_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2551_; 
lean_del_object(v___x_2517_);
v_toSignature_2523_ = lean_ctor_get(v_decl_2508_, 0);
v_value_2524_ = lean_ctor_get(v_decl_2508_, 1);
v_recursive_2525_ = lean_ctor_get_uint8(v_decl_2508_, sizeof(void*)*3);
v_inlineAttr_x3f_2526_ = lean_ctor_get(v_decl_2508_, 2);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_decl_2508_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2528_ = v_decl_2508_;
v_isShared_2529_ = v_isSharedCheck_2551_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_inlineAttr_x3f_2526_);
lean_inc(v_value_2524_);
lean_inc(v_toSignature_2523_);
lean_dec(v_decl_2508_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2551_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___f_2530_; lean_object* v___x_2531_; 
lean_inc_ref(v_toSignature_2523_);
v___f_2530_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2530_, 0, v_toSignature_2523_);
v___x_2531_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v___f_2530_, v_value_2524_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2542_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2542_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2542_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v_a_2532_);
v___x_2537_ = v___x_2528_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_toSignature_2523_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_a_2532_);
lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_inlineAttr_x3f_2526_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, sizeof(void*)*3, v_recursive_2525_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2537_);
v___x_2539_ = v___x_2534_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_del_object(v___x_2528_);
lean_dec(v_inlineAttr_x3f_2526_);
lean_dec_ref(v_toSignature_2523_);
v_a_2543_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2531_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2531_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v_decl_2508_);
v_a_2553_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2514_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2514_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object* v_decl_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(v_decl_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
return v_res_2567_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__2));
v___x_2574_ = 2;
v___x_2575_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__1));
v___x_2576_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_2575_, v___x_2574_, v___x_2573_, v___x_2572_);
return v___x_2576_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse(void){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_obj_once(&l_Lean_Compiler_LCNF_expandResetReuse___closed__3, &l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3);
return v___x_2577_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_unsigned_to_nat(2743268278u);
v___x_2634_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2635_ = l_Lean_Name_num___override(v___x_2634_, v___x_2633_);
return v___x_2635_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2638_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2639_ = l_Lean_Name_str___override(v___x_2638_, v___x_2637_);
return v___x_2639_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2642_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2643_ = l_Lean_Name_str___override(v___x_2642_, v___x_2641_);
return v___x_2643_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = lean_unsigned_to_nat(2u);
v___x_2645_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2646_ = l_Lean_Name_num___override(v___x_2645_, v___x_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2648_; uint8_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2649_ = 1;
v___x_2650_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2651_ = l_Lean_registerTraceClass(v___x_2648_, v___x_2649_, v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
return v_res_2653_;
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
