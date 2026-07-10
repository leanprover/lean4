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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_2795__overap_43_; lean_object* v___x_44_; 
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
v___x_2795__overap_43_ = lean_panic_fn_borrowed(v___f_42_, v_msg_5_);
lean_dec_ref(v___f_42_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
v___x_44_ = lean_apply_5(v___x_2795__overap_43_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
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
lean_object* v___y_100_; lean_object* v___y_121_; lean_object* v___y_122_; lean_object* v___y_123_; lean_object* v_snd_127_; lean_object* v_fst_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_274_; 
v_snd_127_ = lean_ctor_get(v_a_93_, 1);
v_fst_128_ = lean_ctor_get(v_a_93_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_a_93_);
if (v_isSharedCheck_274_ == 0)
{
v___x_130_ = v_a_93_;
v_isShared_131_ = v_isSharedCheck_274_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_snd_127_);
lean_inc(v_fst_128_);
lean_dec(v_a_93_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_274_;
goto v_resetjp_129_;
}
v___jp_99_:
{
if (lean_obj_tag(v___y_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_111_; 
v_a_101_ = lean_ctor_get(v___y_100_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___y_100_);
if (v_isSharedCheck_111_ == 0)
{
v___x_103_ = v___y_100_;
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___y_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
if (lean_obj_tag(v_a_101_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; 
v_a_105_ = lean_ctor_get(v_a_101_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v_a_101_, 1);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v_a_105_);
v___x_107_ = v___x_103_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
else
{
lean_object* v_a_109_; 
lean_del_object(v___x_103_);
v_a_109_ = lean_ctor_get(v_a_101_, 0);
lean_inc(v_a_109_);
lean_dec_ref_known(v_a_101_, 1);
v_a_93_ = v_a_109_;
goto _start;
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_a_112_ = lean_ctor_get(v___y_100_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___y_100_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___y_100_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___y_100_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
v___jp_120_:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v___y_123_);
lean_ctor_set(v___x_124_, 1, v___y_122_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___y_121_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v_a_93_ = v___x_125_;
goto _start;
}
v_resetjp_129_:
{
lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_273_; 
v_fst_132_ = lean_ctor_get(v_snd_127_, 0);
v_snd_133_ = lean_ctor_get(v_snd_127_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_snd_127_);
if (v_isSharedCheck_273_ == 0)
{
v___x_135_ = v_snd_127_;
v_isShared_136_ = v_isSharedCheck_273_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_snd_133_);
lean_inc(v_fst_132_);
lean_dec(v_snd_127_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_273_;
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
v___y_100_ = v___x_184_;
goto v___jp_99_;
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
v___y_100_ = v___x_198_;
goto v___jp_99_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_nat_sub(v___x_138_, v___x_137_);
v___x_200_ = lean_array_get(v___x_147_, v_fst_128_, v___x_199_);
lean_dec(v___x_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_decl_213_; lean_object* v_value_214_; 
v_decl_213_ = lean_ctor_get(v___x_200_, 0);
lean_inc_ref(v_decl_213_);
v_value_214_ = lean_ctor_get(v_decl_213_, 3);
lean_inc(v_value_214_);
if (lean_obj_tag(v_value_214_) == 6)
{
lean_object* v_fvarId_215_; lean_object* v_i_216_; lean_object* v_var_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_250_; 
v_fvarId_215_ = lean_ctor_get(v_decl_213_, 0);
lean_inc(v_fvarId_215_);
lean_dec_ref(v_decl_213_);
v_i_216_ = lean_ctor_get(v_value_214_, 0);
v_var_217_ = lean_ctor_get(v_value_214_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_value_214_);
if (v_isSharedCheck_250_ == 0)
{
v___x_219_ = v_value_214_;
v_isShared_220_ = v_isSharedCheck_250_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_var_217_);
lean_inc(v_i_216_);
lean_dec(v_value_214_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_250_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint8_t v___y_222_; uint8_t v___x_248_; 
v___x_248_ = l_Lean_instBEqFVarId_beq(v_fvarId_215_, v_fvarId_191_);
lean_dec(v_fvarId_215_);
if (v___x_248_ == 0)
{
lean_dec(v_var_217_);
v___y_222_ = v___x_248_;
goto v___jp_221_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = l_Lean_instBEqFVarId_beq(v_targetId_92_, v_var_217_);
lean_dec(v_var_217_);
v___y_222_ = v___x_249_;
goto v___jp_221_;
}
v___jp_221_:
{
uint8_t v___x_223_; 
v___x_223_ = lean_bool_not(v___y_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_del_object(v___x_219_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_array_get_borrowed(v___x_224_, v_snd_133_, v_i_216_);
if (lean_obj_tag(v___x_225_) == 0)
{
if (v___x_223_ == 0)
{
lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_240_; 
lean_inc(v_n_192_);
lean_inc(v_fvarId_191_);
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; lean_object* v_unused_242_; 
v_unused_241_ = lean_ctor_get(v___x_150_, 1);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_242_);
v___x_227_ = v___x_150_;
v_isShared_228_ = v_isSharedCheck_240_;
goto v_resetjp_226_;
}
else
{
lean_dec(v___x_150_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_240_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_229_ = lean_array_pop(v_fst_128_);
v___x_230_ = lean_array_pop(v___x_229_);
lean_inc(v_fvarId_191_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v_fvarId_191_);
v___x_232_ = lean_array_set(v_snd_133_, v_i_216_, v___x_231_);
lean_dec(v_i_216_);
v___x_233_ = lean_array_push(v_fst_132_, v___x_200_);
v___x_234_ = lean_nat_dec_eq(v_n_192_, v___x_148_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_nat_sub(v_n_192_, v___x_148_);
lean_dec(v_n_192_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 1, v___x_235_);
v___x_237_ = v___x_227_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_fvarId_191_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_235_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, sizeof(void*)*2, v_check_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, sizeof(void*)*2 + 1, v_persistent_194_);
v___x_237_ = v_reuseFailAlloc_239_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; 
v___x_238_ = lean_array_push(v___x_233_, v___x_237_);
v___y_121_ = v___x_230_;
v___y_122_ = v___x_232_;
v___y_123_ = v___x_238_;
goto v___jp_120_;
}
}
else
{
lean_del_object(v___x_227_);
lean_dec(v_n_192_);
lean_dec(v_fvarId_191_);
v___y_121_ = v___x_230_;
v___y_122_ = v___x_232_;
v___y_123_ = v___x_233_;
goto v___jp_120_;
}
}
}
else
{
lean_dec(v_i_216_);
goto v___jp_201_;
}
}
else
{
lean_dec(v_i_216_);
goto v___jp_201_;
}
}
else
{
lean_object* v___x_244_; 
lean_dec(v_i_216_);
lean_dec_ref_known(v___x_200_, 1);
lean_dec_ref_known(v___x_150_, 2);
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 0);
lean_ctor_set(v___x_219_, 1, v_snd_133_);
lean_ctor_set(v___x_219_, 0, v_fst_132_);
v___x_244_ = v___x_219_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_fst_132_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_snd_133_);
v___x_244_ = v_reuseFailAlloc_247_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_fst_128_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
}
}
}
else
{
lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_269_; 
lean_dec_ref_known(v___x_150_, 2);
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; 
v_unused_270_ = lean_ctor_get(v___x_200_, 0);
lean_dec(v_unused_270_);
v___x_252_ = v___x_200_;
v_isShared_253_ = v_isSharedCheck_269_;
goto v_resetjp_251_;
}
else
{
lean_dec(v___x_200_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_269_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_fvarId_254_; lean_object* v_binderName_255_; lean_object* v_type_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_267_; 
v_fvarId_254_ = lean_ctor_get(v_decl_213_, 0);
v_binderName_255_ = lean_ctor_get(v_decl_213_, 1);
v_type_256_ = lean_ctor_get(v_decl_213_, 2);
v_isSharedCheck_267_ = !lean_is_exclusive(v_decl_213_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v_decl_213_, 3);
lean_dec(v_unused_268_);
v___x_258_ = v_decl_213_;
v_isShared_259_ = v_isSharedCheck_267_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_type_256_);
lean_inc(v_binderName_255_);
lean_inc(v_fvarId_254_);
lean_dec(v_decl_213_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_267_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_fvarId_254_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_binderName_255_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_type_256_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_value_214_);
v___x_261_ = v_reuseFailAlloc_266_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_261_);
v___x_263_ = v___x_252_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_263_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec_ref(v___x_263_);
v___y_100_ = v___x_264_;
goto v___jp_99_;
}
}
}
}
}
}
else
{
lean_object* v___x_271_; 
lean_dec_ref_known(v___x_150_, 2);
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v___x_271_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_200_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___x_200_);
v___y_100_ = v___x_271_;
goto v___jp_99_;
}
v___jp_201_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_202_ = lean_array_push(v_fst_132_, v___x_150_);
v___x_203_ = lean_array_push(v___x_202_, v___x_200_);
v___x_204_ = lean_array_pop(v_fst_128_);
v___x_205_ = lean_array_pop(v___x_204_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_203_);
v___x_207_ = v___x_135_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_snd_133_);
v___x_207_ = v_reuseFailAlloc_212_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_209_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_207_);
lean_ctor_set(v___x_130_, 0, v___x_205_);
v___x_209_ = v___x_130_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_207_);
v___x_209_ = v_reuseFailAlloc_211_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
v_a_93_ = v___x_209_;
goto _start;
}
}
}
}
}
default: 
{
lean_object* v___x_272_; 
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v___x_272_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_150_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___x_150_);
v___y_100_ = v___x_272_;
goto v___jp_99_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(lean_object* v_targetId_275_, lean_object* v_a_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_275_, v_a_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v_targetId_275_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object* v_nFields_285_, lean_object* v_targetId_286_, lean_object* v_ds_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_keep_293_; lean_object* v___x_294_; lean_object* v_mask_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_keep_293_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_294_ = lean_box(0);
v_mask_295_ = lean_mk_array(v_nFields_285_, v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_keep_293_);
lean_ctor_set(v___x_296_, 1, v_mask_295_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_ds_287_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_286_, v___x_297_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_319_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_319_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_319_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_319_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_snd_303_; lean_object* v_fst_304_; lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_318_; 
v_snd_303_ = lean_ctor_get(v_a_299_, 1);
lean_inc(v_snd_303_);
v_fst_304_ = lean_ctor_get(v_a_299_, 0);
lean_inc(v_fst_304_);
lean_dec(v_a_299_);
v_fst_305_ = lean_ctor_get(v_snd_303_, 0);
v_snd_306_ = lean_ctor_get(v_snd_303_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_snd_303_);
if (v_isSharedCheck_318_ == 0)
{
v___x_308_ = v_snd_303_;
v_isShared_309_ = v_isSharedCheck_318_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_snd_306_);
lean_inc(v_fst_305_);
lean_dec(v_snd_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_318_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_310_ = l_Array_reverse___redArg(v_fst_305_);
v___x_311_ = l_Array_append___redArg(v_fst_304_, v___x_310_);
lean_dec_ref(v___x_310_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_311_);
v___x_313_ = v___x_308_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_snd_306_);
v___x_313_ = v_reuseFailAlloc_317_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_315_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_313_);
v___x_315_ = v___x_301_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_a_320_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_298_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_298_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object* v_nFields_328_, lean_object* v_targetId_329_, lean_object* v_ds_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_328_, v_targetId_329_, v_ds_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_targetId_329_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object* v_targetId_337_, lean_object* v_inst_338_, lean_object* v_a_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_337_, v_a_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
return v___x_345_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object* v_discr_371_, lean_object* v_discrType_372_, lean_object* v_resultType_373_, lean_object* v_t_374_, lean_object* v_e_375_){
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object* v_discr_390_, lean_object* v_discrType_391_, lean_object* v_resultType_392_, lean_object* v_t_393_, lean_object* v_e_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_390_, v_discrType_391_, v_resultType_392_, v_t_393_, v_e_394_);
lean_dec_ref(v_discrType_391_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object* v_discr_397_, lean_object* v_discrType_398_, lean_object* v_resultType_399_, lean_object* v_t_400_, lean_object* v_e_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_397_, v_discrType_398_, v_resultType_399_, v_t_400_, v_e_401_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object* v_discr_408_, lean_object* v_discrType_409_, lean_object* v_resultType_410_, lean_object* v_t_411_, lean_object* v_e_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(v_discr_408_, v_discrType_409_, v_resultType_410_, v_t_411_, v_e_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_discrType_409_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object* v_msg_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_421_ = lean_panic_fn_borrowed(v___x_420_, v_msg_419_);
return v___x_421_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_425_ = lean_unsigned_to_nat(11u);
v___x_426_ = lean_unsigned_to_nat(138u);
v___x_427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0));
v___x_428_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_429_ = l_mkPanicMessageWithDecl(v___x_428_, v___x_427_, v___x_426_, v___x_425_, v___x_424_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object* v_targetId_430_, size_t v_sz_431_, size_t v_i_432_, lean_object* v_bs_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_lt(v_i_432_, v_sz_431_);
if (v___x_434_ == 0)
{
lean_dec(v_targetId_430_);
return v_bs_433_;
}
else
{
lean_object* v_v_435_; lean_object* v___x_436_; lean_object* v_bs_x27_437_; lean_object* v___y_439_; 
v_v_435_ = lean_array_uget(v_bs_433_, v_i_432_);
v___x_436_ = lean_unsigned_to_nat(0u);
v_bs_x27_437_ = lean_array_uset(v_bs_433_, v_i_432_, v___x_436_);
switch(lean_obj_tag(v_v_435_))
{
case 3:
{
lean_object* v_i_444_; lean_object* v_y_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
v_i_444_ = lean_ctor_get(v_v_435_, 1);
v_y_445_ = lean_ctor_get(v_v_435_, 2);
v_isSharedCheck_452_ = !lean_is_exclusive(v_v_435_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; 
v_unused_453_ = lean_ctor_get(v_v_435_, 0);
lean_dec(v_unused_453_);
v___x_447_ = v_v_435_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_y_445_);
lean_inc(v_i_444_);
lean_dec(v_v_435_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
lean_inc(v_targetId_430_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v_targetId_430_);
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_targetId_430_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_i_444_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_y_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
v___y_439_ = v___x_450_;
goto v___jp_438_;
}
}
}
case 5:
{
lean_object* v_i_454_; lean_object* v_offset_455_; lean_object* v_y_456_; lean_object* v_ty_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_i_454_ = lean_ctor_get(v_v_435_, 1);
v_offset_455_ = lean_ctor_get(v_v_435_, 2);
v_y_456_ = lean_ctor_get(v_v_435_, 3);
v_ty_457_ = lean_ctor_get(v_v_435_, 4);
v_isSharedCheck_464_ = !lean_is_exclusive(v_v_435_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v_v_435_, 0);
lean_dec(v_unused_465_);
v___x_459_ = v_v_435_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_ty_457_);
lean_inc(v_y_456_);
lean_inc(v_offset_455_);
lean_inc(v_i_454_);
lean_dec(v_v_435_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
lean_inc(v_targetId_430_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v_targetId_430_);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_targetId_430_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_i_454_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_offset_455_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_y_456_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_ty_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
v___y_439_ = v___x_462_;
goto v___jp_438_;
}
}
}
case 4:
{
lean_object* v_i_466_; lean_object* v_y_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
v_i_466_ = lean_ctor_get(v_v_435_, 1);
v_y_467_ = lean_ctor_get(v_v_435_, 2);
v_isSharedCheck_474_ = !lean_is_exclusive(v_v_435_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_v_435_, 0);
lean_dec(v_unused_475_);
v___x_469_ = v_v_435_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_y_467_);
lean_inc(v_i_466_);
lean_dec(v_v_435_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
lean_inc(v_targetId_430_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v_targetId_430_);
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_targetId_430_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_i_466_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_y_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
v___y_439_ = v___x_472_;
goto v___jp_438_;
}
}
}
default: 
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v_v_435_);
v___x_476_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2);
v___x_477_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(v___x_476_);
v___y_439_ = v___x_477_;
goto v___jp_438_;
}
}
v___jp_438_:
{
size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; 
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_add(v_i_432_, v___x_440_);
v___x_442_ = lean_array_uset(v_bs_x27_437_, v_i_432_, v___y_439_);
v_i_432_ = v___x_441_;
v_bs_433_ = v___x_442_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object* v_targetId_478_, lean_object* v_sz_479_, lean_object* v_i_480_, lean_object* v_bs_481_){
_start:
{
size_t v_sz_boxed_482_; size_t v_i_boxed_483_; lean_object* v_res_484_; 
v_sz_boxed_482_ = lean_unbox_usize(v_sz_479_);
lean_dec(v_sz_479_);
v_i_boxed_483_ = lean_unbox_usize(v_i_480_);
lean_dec(v_i_480_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_478_, v_sz_boxed_482_, v_i_boxed_483_, v_bs_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object* v_targetId_485_, lean_object* v_sets_486_){
_start:
{
size_t v_sz_488_; size_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_sz_488_ = lean_array_size(v_sets_486_);
v___x_489_ = ((size_t)0ULL);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_485_, v_sz_488_, v___x_489_, v_sets_486_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object* v_targetId_492_, lean_object* v_sets_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_492_, v_sets_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object* v_targetId_496_, lean_object* v_sets_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_496_, v_sets_497_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object* v_targetId_504_, lean_object* v_sets_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(v_targetId_504_, v_sets_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object* v_fvarId_512_, lean_object* v_i_513_, lean_object* v_y_514_, lean_object* v_a_515_){
_start:
{
if (lean_obj_tag(v_y_514_) == 0)
{
uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = 0;
v___x_518_ = lean_box(v___x_517_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
else
{
lean_object* v_fvarId_520_; uint8_t v___x_521_; lean_object* v___x_522_; 
v_fvarId_520_ = lean_ctor_get(v_y_514_, 0);
v___x_521_ = 1;
v___x_522_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_521_, v_fvarId_520_, v_a_515_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_550_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_550_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_550_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_550_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
if (lean_obj_tag(v_a_523_) == 1)
{
lean_object* v_val_527_; 
v_val_527_ = lean_ctor_get(v_a_523_, 0);
lean_inc(v_val_527_);
lean_dec_ref_known(v_a_523_, 1);
if (lean_obj_tag(v_val_527_) == 6)
{
lean_object* v_i_528_; lean_object* v_var_529_; uint8_t v___x_530_; 
v_i_528_ = lean_ctor_get(v_val_527_, 0);
lean_inc(v_i_528_);
v_var_529_ = lean_ctor_get(v_val_527_, 1);
lean_inc(v_var_529_);
lean_dec_ref_known(v_val_527_, 2);
v___x_530_ = lean_nat_dec_eq(v_i_513_, v_i_528_);
lean_dec(v_i_528_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_533_; 
lean_dec(v_var_529_);
v___x_531_ = lean_box(v___x_530_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_531_);
v___x_533_ = v___x_525_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
else
{
uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = l_Lean_instBEqFVarId_beq(v_fvarId_512_, v_var_529_);
lean_dec(v_var_529_);
v___x_536_ = lean_box(v___x_535_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_536_);
v___x_538_ = v___x_525_;
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
}
else
{
uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
lean_dec(v_val_527_);
v___x_540_ = 0;
v___x_541_ = lean_box(v___x_540_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_541_);
v___x_543_ = v___x_525_;
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
lean_dec(v_a_523_);
v___x_545_ = 0;
v___x_546_ = lean_box(v___x_545_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_546_);
v___x_548_ = v___x_525_;
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
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_551_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_522_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_522_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object* v_fvarId_559_, lean_object* v_i_560_, lean_object* v_y_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_559_, v_i_560_, v_y_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec(v_y_561_);
lean_dec(v_i_560_);
lean_dec(v_fvarId_559_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object* v_fvarId_565_, lean_object* v_i_566_, lean_object* v_y_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_565_, v_i_566_, v_y_567_, v_a_569_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object* v_fvarId_574_, lean_object* v_i_575_, lean_object* v_y_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(v_fvarId_574_, v_i_575_, v_y_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_y_576_);
lean_dec(v_i_575_);
lean_dec(v_fvarId_574_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object* v_fvarId_583_, lean_object* v_i_584_, lean_object* v_y_585_, lean_object* v_a_586_){
_start:
{
uint8_t v___x_588_; lean_object* v___x_589_; 
v___x_588_ = 1;
v___x_589_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_588_, v_y_585_, v_a_586_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_617_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_617_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_617_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_617_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
if (lean_obj_tag(v_a_590_) == 1)
{
lean_object* v_val_594_; 
v_val_594_ = lean_ctor_get(v_a_590_, 0);
lean_inc(v_val_594_);
lean_dec_ref_known(v_a_590_, 1);
if (lean_obj_tag(v_val_594_) == 7)
{
lean_object* v_i_595_; lean_object* v_var_596_; uint8_t v___x_597_; 
v_i_595_ = lean_ctor_get(v_val_594_, 0);
lean_inc(v_i_595_);
v_var_596_ = lean_ctor_get(v_val_594_, 1);
lean_inc(v_var_596_);
lean_dec_ref_known(v_val_594_, 2);
v___x_597_ = lean_nat_dec_eq(v_i_584_, v_i_595_);
lean_dec(v_i_595_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_600_; 
lean_dec(v_var_596_);
v___x_598_ = lean_box(v___x_597_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_598_);
v___x_600_ = v___x_592_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
else
{
uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_602_ = l_Lean_instBEqFVarId_beq(v_fvarId_583_, v_var_596_);
lean_dec(v_var_596_);
v___x_603_ = lean_box(v___x_602_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_603_);
v___x_605_ = v___x_592_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
lean_dec(v_val_594_);
v___x_607_ = 0;
v___x_608_ = lean_box(v___x_607_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_608_);
v___x_610_ = v___x_592_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
uint8_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
lean_dec(v_a_590_);
v___x_612_ = 0;
v___x_613_ = lean_box(v___x_612_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_613_);
v___x_615_ = v___x_592_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
v_a_618_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_589_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_589_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object* v_fvarId_626_, lean_object* v_i_627_, lean_object* v_y_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_626_, v_i_627_, v_y_628_, v_a_629_);
lean_dec(v_a_629_);
lean_dec(v_y_628_);
lean_dec(v_i_627_);
lean_dec(v_fvarId_626_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object* v_fvarId_632_, lean_object* v_i_633_, lean_object* v_y_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_632_, v_i_633_, v_y_634_, v_a_636_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object* v_fvarId_641_, lean_object* v_i_642_, lean_object* v_y_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(v_fvarId_641_, v_i_642_, v_y_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_y_643_);
lean_dec(v_i_642_);
lean_dec(v_fvarId_641_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object* v_fvarId_650_, lean_object* v_i_651_, lean_object* v_offset_652_, lean_object* v_y_653_, lean_object* v_a_654_){
_start:
{
uint8_t v___x_656_; lean_object* v___x_657_; 
v___x_656_ = 1;
v___x_657_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_656_, v_y_653_, v_a_654_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_689_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_689_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_689_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_689_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
if (lean_obj_tag(v_a_658_) == 1)
{
lean_object* v_val_662_; 
v_val_662_ = lean_ctor_get(v_a_658_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v_a_658_, 1);
if (lean_obj_tag(v_val_662_) == 8)
{
lean_object* v_n_663_; lean_object* v_offset_664_; lean_object* v_var_665_; uint8_t v___y_667_; uint8_t v___x_677_; 
v_n_663_ = lean_ctor_get(v_val_662_, 0);
lean_inc(v_n_663_);
v_offset_664_ = lean_ctor_get(v_val_662_, 1);
lean_inc(v_offset_664_);
v_var_665_ = lean_ctor_get(v_val_662_, 2);
lean_inc(v_var_665_);
lean_dec_ref_known(v_val_662_, 3);
v___x_677_ = lean_nat_dec_eq(v_i_651_, v_n_663_);
lean_dec(v_n_663_);
if (v___x_677_ == 0)
{
lean_dec(v_offset_664_);
v___y_667_ = v___x_677_;
goto v___jp_666_;
}
else
{
uint8_t v___x_678_; 
v___x_678_ = lean_nat_dec_eq(v_offset_652_, v_offset_664_);
lean_dec(v_offset_664_);
v___y_667_ = v___x_678_;
goto v___jp_666_;
}
v___jp_666_:
{
if (v___y_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_670_; 
lean_dec(v_var_665_);
v___x_668_ = lean_box(v___y_667_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_668_);
v___x_670_ = v___x_660_;
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
v___x_672_ = l_Lean_instBEqFVarId_beq(v_fvarId_650_, v_var_665_);
lean_dec(v_var_665_);
v___x_673_ = lean_box(v___x_672_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_673_);
v___x_675_ = v___x_660_;
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
uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
lean_dec(v_val_662_);
v___x_679_ = 0;
v___x_680_ = lean_box(v___x_679_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_680_);
v___x_682_ = v___x_660_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
else
{
uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
lean_dec(v_a_658_);
v___x_684_ = 0;
v___x_685_ = lean_box(v___x_684_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_685_);
v___x_687_ = v___x_660_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_657_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_657_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object* v_fvarId_698_, lean_object* v_i_699_, lean_object* v_offset_700_, lean_object* v_y_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_698_, v_i_699_, v_offset_700_, v_y_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec(v_y_701_);
lean_dec(v_offset_700_);
lean_dec(v_i_699_);
lean_dec(v_fvarId_698_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object* v_fvarId_705_, lean_object* v_i_706_, lean_object* v_offset_707_, lean_object* v_y_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_705_, v_i_706_, v_offset_707_, v_y_708_, v_a_710_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object* v_fvarId_715_, lean_object* v_i_716_, lean_object* v_offset_717_, lean_object* v_y_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(v_fvarId_715_, v_i_716_, v_offset_717_, v_y_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_y_718_);
lean_dec(v_offset_717_);
lean_dec(v_i_716_);
lean_dec(v_fvarId_715_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object* v_msg_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_toApplicative_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_767_; 
v___x_731_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_732_ = l_StateRefT_x27_instMonad___redArg(v___x_731_);
v_toApplicative_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v___x_732_, 1);
lean_dec(v_unused_768_);
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_767_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_toApplicative_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_767_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_toFunctor_737_; lean_object* v_toSeq_738_; lean_object* v_toSeqLeft_739_; lean_object* v_toSeqRight_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_765_; 
v_toFunctor_737_ = lean_ctor_get(v_toApplicative_733_, 0);
v_toSeq_738_ = lean_ctor_get(v_toApplicative_733_, 2);
v_toSeqLeft_739_ = lean_ctor_get(v_toApplicative_733_, 3);
v_toSeqRight_740_ = lean_ctor_get(v_toApplicative_733_, 4);
v_isSharedCheck_765_ = !lean_is_exclusive(v_toApplicative_733_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_toApplicative_733_, 1);
lean_dec(v_unused_766_);
v___x_742_ = v_toApplicative_733_;
v_isShared_743_ = v_isSharedCheck_765_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_toSeqRight_740_);
lean_inc(v_toSeqLeft_739_);
lean_inc(v_toSeq_738_);
lean_inc(v_toFunctor_737_);
lean_dec(v_toApplicative_733_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_765_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_753_; 
v___f_744_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_745_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_737_);
v___f_746_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_746_, 0, v_toFunctor_737_);
v___f_747_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_747_, 0, v_toFunctor_737_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___f_746_);
lean_ctor_set(v___x_748_, 1, v___f_747_);
v___f_749_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_749_, 0, v_toSeqRight_740_);
v___f_750_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_750_, 0, v_toSeqLeft_739_);
v___f_751_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_751_, 0, v_toSeq_738_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 4, v___f_749_);
lean_ctor_set(v___x_742_, 3, v___f_750_);
lean_ctor_set(v___x_742_, 2, v___f_751_);
lean_ctor_set(v___x_742_, 1, v___f_744_);
lean_ctor_set(v___x_742_, 0, v___x_748_);
v___x_753_ = v___x_742_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___f_744_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v___f_751_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v___f_750_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v___f_749_);
v___x_753_ = v_reuseFailAlloc_764_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___f_745_);
lean_ctor_set(v___x_735_, 0, v___x_753_);
v___x_755_ = v___x_735_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___f_745_);
v___x_755_ = v_reuseFailAlloc_763_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___f_760_; lean_object* v___x_994__overap_761_; lean_object* v___x_762_; 
v___x_756_ = l_StateRefT_x27_instMonad___redArg(v___x_755_);
v___x_757_ = 0;
v___x_758_ = lean_box(v___x_757_);
v___x_759_ = l_instInhabitedOfMonad___redArg(v___x_756_, v___x_758_);
v___f_760_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_760_, 0, v___x_759_);
v___x_994__overap_761_ = lean_panic_fn_borrowed(v___f_760_, v_msg_725_);
lean_dec_ref(v___f_760_);
lean_inc(v___y_729_);
lean_inc_ref(v___y_728_);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
v___x_762_ = lean_apply_5(v___x_994__overap_761_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, lean_box(0));
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object* v_msg_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v_msg_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
return v_res_775_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_778_ = lean_unsigned_to_nat(13u);
v___x_779_ = lean_unsigned_to_nat(174u);
v___x_780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0));
v___x_781_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_782_ = l_mkPanicMessageWithDecl(v___x_781_, v___x_780_, v___x_779_, v___x_778_, v___x_777_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object* v_selfId_783_, lean_object* v_as_784_, size_t v_sz_785_, size_t v_i_786_, lean_object* v_b_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_a_794_; uint8_t v___x_798_; 
v___x_798_ = lean_usize_dec_lt(v_i_786_, v_sz_785_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v_b_787_);
return v___x_799_;
}
else
{
lean_object* v_fst_800_; lean_object* v_snd_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_838_; 
v_fst_800_ = lean_ctor_get(v_b_787_, 0);
v_snd_801_ = lean_ctor_get(v_b_787_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_b_787_);
if (v_isSharedCheck_838_ == 0)
{
v___x_803_ = v_b_787_;
v_isShared_804_ = v_isSharedCheck_838_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_snd_801_);
lean_inc(v_fst_800_);
lean_dec(v_b_787_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_838_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_a_805_; lean_object* v___y_807_; 
v_a_805_ = lean_array_uget_borrowed(v_as_784_, v_i_786_);
switch(lean_obj_tag(v_a_805_))
{
case 3:
{
lean_object* v_i_826_; lean_object* v_y_827_; lean_object* v___x_828_; 
v_i_826_ = lean_ctor_get(v_a_805_, 1);
v_y_827_ = lean_ctor_get(v_a_805_, 2);
v___x_828_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_selfId_783_, v_i_826_, v_y_827_, v___y_789_);
v___y_807_ = v___x_828_;
goto v___jp_806_;
}
case 4:
{
lean_object* v_i_829_; lean_object* v_y_830_; lean_object* v___x_831_; 
v_i_829_ = lean_ctor_get(v_a_805_, 1);
v_y_830_ = lean_ctor_get(v_a_805_, 2);
v___x_831_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_selfId_783_, v_i_829_, v_y_830_, v___y_789_);
v___y_807_ = v___x_831_;
goto v___jp_806_;
}
case 5:
{
lean_object* v_i_832_; lean_object* v_offset_833_; lean_object* v_y_834_; lean_object* v___x_835_; 
v_i_832_ = lean_ctor_get(v_a_805_, 1);
v_offset_833_ = lean_ctor_get(v_a_805_, 2);
v_y_834_ = lean_ctor_get(v_a_805_, 3);
v___x_835_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_selfId_783_, v_i_832_, v_offset_833_, v_y_834_, v___y_789_);
v___y_807_ = v___x_835_;
goto v___jp_806_;
}
default: 
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1);
v___x_837_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v___x_836_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
v___y_807_ = v___x_837_;
goto v___jp_806_;
}
}
v___jp_806_:
{
if (lean_obj_tag(v___y_807_) == 0)
{
lean_object* v_a_808_; uint8_t v___x_809_; 
v_a_808_ = lean_ctor_get(v___y_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___y_807_, 1);
v___x_809_ = lean_unbox(v_a_808_);
lean_dec(v_a_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_812_; 
lean_inc(v_a_805_);
v___x_810_ = lean_array_push(v_fst_800_, v_a_805_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_810_);
v___x_812_ = v___x_803_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_snd_801_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v_a_794_ = v___x_812_;
goto v___jp_793_;
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_inc(v_a_805_);
v___x_814_ = lean_array_push(v_snd_801_, v_a_805_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_814_);
v___x_816_ = v___x_803_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_fst_800_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
v_a_794_ = v___x_816_;
goto v___jp_793_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_del_object(v___x_803_);
lean_dec(v_snd_801_);
lean_dec(v_fst_800_);
v_a_818_ = lean_ctor_get(v___y_807_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___y_807_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___y_807_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___y_807_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
v___jp_793_:
{
size_t v___x_795_; size_t v___x_796_; 
v___x_795_ = ((size_t)1ULL);
v___x_796_ = lean_usize_add(v_i_786_, v___x_795_);
v_i_786_ = v___x_796_;
v_b_787_ = v_a_794_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object* v_selfId_839_, lean_object* v_as_840_, lean_object* v_sz_841_, lean_object* v_i_842_, lean_object* v_b_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
size_t v_sz_boxed_849_; size_t v_i_boxed_850_; lean_object* v_res_851_; 
v_sz_boxed_849_ = lean_unbox_usize(v_sz_841_);
lean_dec(v_sz_841_);
v_i_boxed_850_ = lean_unbox_usize(v_i_842_);
lean_dec(v_i_842_);
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_839_, v_as_840_, v_sz_boxed_849_, v_i_boxed_850_, v_b_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v_as_840_);
lean_dec(v_selfId_839_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object* v_selfId_854_, lean_object* v_sets_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_861_; size_t v_sz_862_; size_t v___x_863_; lean_object* v___x_864_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0));
v_sz_862_ = lean_array_size(v_sets_855_);
v___x_863_ = ((size_t)0ULL);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_854_, v_sets_855_, v_sz_862_, v___x_863_, v___x_861_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_881_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_881_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_881_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_881_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_880_; 
v_fst_869_ = lean_ctor_get(v_a_865_, 0);
v_snd_870_ = lean_ctor_get(v_a_865_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_a_865_);
if (v_isSharedCheck_880_ == 0)
{
v___x_872_ = v_a_865_;
v_isShared_873_ = v_isSharedCheck_880_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_snd_870_);
lean_inc(v_fst_869_);
lean_dec(v_a_865_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_880_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v_fst_869_);
lean_ctor_set(v___x_872_, 0, v_snd_870_);
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_snd_870_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_fst_869_);
v___x_875_ = v_reuseFailAlloc_879_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_875_);
v___x_877_ = v___x_867_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
else
{
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object* v_selfId_882_, lean_object* v_sets_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_selfId_882_, v_sets_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec_ref(v_sets_883_);
lean_dec(v_selfId_882_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object* v_target_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_snd_893_; 
v_snd_893_ = lean_ctor_get(v_a_891_, 1);
lean_inc(v_snd_893_);
switch(lean_obj_tag(v_snd_893_))
{
case 7:
{
lean_object* v_fst_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_913_; 
v_fst_894_ = lean_ctor_get(v_a_891_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_891_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v_a_891_, 1);
lean_dec(v_unused_914_);
v___x_896_ = v_a_891_;
v_isShared_897_ = v_isSharedCheck_913_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_fst_894_);
lean_dec(v_a_891_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_913_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_fvarId_898_; lean_object* v_k_899_; uint8_t v___x_900_; uint8_t v___x_901_; 
v_fvarId_898_ = lean_ctor_get(v_snd_893_, 0);
v_k_899_ = lean_ctor_get(v_snd_893_, 3);
v___x_900_ = l_Lean_instBEqFVarId_beq(v_target_890_, v_fvarId_898_);
v___x_901_ = lean_bool_not(v___x_900_);
if (v___x_901_ == 0)
{
uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
lean_inc_ref(v_k_899_);
v___x_902_ = 1;
v___x_903_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_902_, v_snd_893_);
lean_dec_ref_known(v_snd_893_, 4);
v___x_904_ = lean_array_push(v_fst_894_, v___x_903_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v_k_899_);
lean_ctor_set(v___x_896_, 0, v___x_904_);
v___x_906_ = v___x_896_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_k_899_);
v___x_906_ = v_reuseFailAlloc_908_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
v_a_891_ = v___x_906_;
goto _start;
}
}
else
{
lean_object* v___x_910_; 
if (v_isShared_897_ == 0)
{
v___x_910_ = v___x_896_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_fst_894_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_snd_893_);
v___x_910_ = v_reuseFailAlloc_912_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
}
case 9:
{
lean_object* v_fst_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_934_; 
v_fst_915_ = lean_ctor_get(v_a_891_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_891_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v_a_891_, 1);
lean_dec(v_unused_935_);
v___x_917_ = v_a_891_;
v_isShared_918_ = v_isSharedCheck_934_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_fst_915_);
lean_dec(v_a_891_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_934_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_fvarId_919_; lean_object* v_k_920_; uint8_t v___x_921_; uint8_t v___x_922_; 
v_fvarId_919_ = lean_ctor_get(v_snd_893_, 0);
v_k_920_ = lean_ctor_get(v_snd_893_, 5);
v___x_921_ = l_Lean_instBEqFVarId_beq(v_target_890_, v_fvarId_919_);
v___x_922_ = lean_bool_not(v___x_921_);
if (v___x_922_ == 0)
{
uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
lean_inc_ref(v_k_920_);
v___x_923_ = 1;
v___x_924_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_923_, v_snd_893_);
lean_dec_ref_known(v_snd_893_, 6);
v___x_925_ = lean_array_push(v_fst_915_, v___x_924_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v_k_920_);
lean_ctor_set(v___x_917_, 0, v___x_925_);
v___x_927_ = v___x_917_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_k_920_);
v___x_927_ = v_reuseFailAlloc_929_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
v_a_891_ = v___x_927_;
goto _start;
}
}
else
{
lean_object* v___x_931_; 
if (v_isShared_918_ == 0)
{
v___x_931_ = v___x_917_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_fst_915_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_snd_893_);
v___x_931_ = v_reuseFailAlloc_933_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
}
}
case 8:
{
lean_object* v_fst_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_955_; 
v_fst_936_ = lean_ctor_get(v_a_891_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v_a_891_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v_a_891_, 1);
lean_dec(v_unused_956_);
v___x_938_ = v_a_891_;
v_isShared_939_ = v_isSharedCheck_955_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_fst_936_);
lean_dec(v_a_891_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_955_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_fvarId_940_; lean_object* v_k_941_; uint8_t v___x_942_; uint8_t v___x_943_; 
v_fvarId_940_ = lean_ctor_get(v_snd_893_, 0);
v_k_941_ = lean_ctor_get(v_snd_893_, 3);
v___x_942_ = l_Lean_instBEqFVarId_beq(v_target_890_, v_fvarId_940_);
v___x_943_ = lean_bool_not(v___x_942_);
if (v___x_943_ == 0)
{
uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
lean_inc_ref(v_k_941_);
v___x_944_ = 1;
v___x_945_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_944_, v_snd_893_);
lean_dec_ref_known(v_snd_893_, 4);
v___x_946_ = lean_array_push(v_fst_936_, v___x_945_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v_k_941_);
lean_ctor_set(v___x_938_, 0, v___x_946_);
v___x_948_ = v___x_938_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_941_);
v___x_948_ = v_reuseFailAlloc_950_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
v_a_891_ = v___x_948_;
goto _start;
}
}
else
{
lean_object* v___x_952_; 
if (v_isShared_939_ == 0)
{
v___x_952_ = v___x_938_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_snd_893_);
v___x_952_ = v_reuseFailAlloc_954_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
}
}
default: 
{
lean_object* v_fst_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_965_; 
v_fst_957_ = lean_ctor_get(v_a_891_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v_a_891_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v_a_891_, 1);
lean_dec(v_unused_966_);
v___x_959_ = v_a_891_;
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_fst_957_);
lean_dec(v_a_891_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_fst_957_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_snd_893_);
v___x_962_ = v_reuseFailAlloc_964_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; 
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object* v_target_967_, lean_object* v_a_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_967_, v_a_968_);
lean_dec(v_target_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object* v_target_971_, lean_object* v_k_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_sets_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_sets_978_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v_sets_978_);
lean_ctor_set(v___x_979_, 1, v_k_972_);
v___x_980_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_971_, v___x_979_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_997_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_997_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_997_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_997_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_996_; 
v_fst_985_ = lean_ctor_get(v_a_981_, 0);
v_snd_986_ = lean_ctor_get(v_a_981_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_a_981_);
if (v_isSharedCheck_996_ == 0)
{
v___x_988_ = v_a_981_;
v_isShared_989_ = v_isSharedCheck_996_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snd_986_);
lean_inc(v_fst_985_);
lean_dec(v_a_981_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_996_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_fst_985_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_snd_986_);
v___x_991_ = v_reuseFailAlloc_995_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_991_);
v___x_993_ = v___x_983_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
else
{
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object* v_target_998_, lean_object* v_k_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_target_998_, v_k_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_target_998_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object* v_target_1006_, lean_object* v_inst_1007_, lean_object* v_a_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_1006_, v_a_1008_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object* v_target_1015_, lean_object* v_inst_1016_, lean_object* v_a_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(v_target_1015_, v_inst_1016_, v_a_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v_target_1015_);
return v_res_1023_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3));
v___x_1032_ = l_Lean_Expr_const___override(v___x_1031_, v___x_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1033_, lean_object* v_mask_1034_, lean_object* v_origAllocId_1035_, lean_object* v_a_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_a_1044_; uint8_t v___x_1048_; 
v___x_1048_ = lean_nat_dec_lt(v_a_1036_, v_upperBound_1033_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec(v_a_1036_);
lean_dec(v_origAllocId_1035_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_b_1037_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_array_fget_borrowed(v_mask_1034_, v_a_1036_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1));
v___x_1052_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1051_, v___y_1039_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = 1;
v___x_1055_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_origAllocId_1035_);
lean_inc(v_a_1036_);
v___x_1056_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_a_1036_);
lean_ctor_set(v___x_1056_, 1, v_origAllocId_1035_);
v___x_1057_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1054_, v_a_1053_, v___x_1055_, v___x_1056_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v_fvarId_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v_fvarId_1059_ = lean_ctor_get(v_a_1058_, 0);
v___x_1060_ = 0;
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_box(0);
lean_inc(v_fvarId_1059_);
v___x_1063_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1063_, 0, v_fvarId_1059_);
lean_ctor_set(v___x_1063_, 1, v___x_1061_);
lean_ctor_set(v___x_1063_, 2, v___x_1062_);
lean_ctor_set(v___x_1063_, 3, v_b_1037_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*4, v___x_1048_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*4 + 1, v___x_1060_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v_a_1058_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v_a_1044_ = v___x_1064_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_b_1037_);
lean_dec(v_a_1036_);
lean_dec(v_origAllocId_1035_);
v_a_1065_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1057_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1057_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_b_1037_);
lean_dec(v_a_1036_);
lean_dec(v_origAllocId_1035_);
v_a_1073_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1052_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1052_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
v_a_1044_ = v_b_1037_;
goto v___jp_1043_;
}
}
v___jp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_a_1036_, v___x_1045_);
lean_dec(v_a_1036_);
v_a_1036_ = v___x_1046_;
v_b_1037_ = v_a_1044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1081_, lean_object* v_mask_1082_, lean_object* v_origAllocId_1083_, lean_object* v_a_1084_, lean_object* v_b_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1081_, v_mask_1082_, v_origAllocId_1083_, v_a_1084_, v_b_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec_ref(v_mask_1082_);
lean_dec(v_upperBound_1081_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object* v_origAllocId_1092_, lean_object* v_mask_1093_, lean_object* v_resetJpId_1094_, lean_object* v_isSharedId_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_code_1109_; lean_object* v___x_1110_; 
lean_inc(v_origAllocId_1092_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_origAllocId_1092_);
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_isSharedId_1095_);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_array_get_size(v_mask_1093_);
v___x_1105_ = lean_unsigned_to_nat(2u);
v___x_1106_ = lean_mk_empty_array_with_capacity(v___x_1105_);
v___x_1107_ = lean_array_push(v___x_1106_, v___x_1101_);
v___x_1108_ = lean_array_push(v___x_1107_, v___x_1102_);
v_code_1109_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1109_, 0, v_resetJpId_1094_);
lean_ctor_set(v_code_1109_, 1, v___x_1108_);
v___x_1110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v___x_1104_, v_mask_1093_, v_origAllocId_1092_, v___x_1103_, v_code_1109_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object* v_origAllocId_1111_, lean_object* v_mask_1112_, lean_object* v_resetJpId_1113_, lean_object* v_isSharedId_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_1111_, v_mask_1112_, v_resetJpId_1113_, v_isSharedId_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec_ref(v_mask_1112_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object* v_upperBound_1121_, lean_object* v_mask_1122_, lean_object* v_origAllocId_1123_, lean_object* v_inst_1124_, lean_object* v_R_1125_, lean_object* v_a_1126_, lean_object* v_b_1127_, lean_object* v_c_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1121_, v_mask_1122_, v_origAllocId_1123_, v_a_1126_, v_b_1127_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1135_, lean_object* v_mask_1136_, lean_object* v_origAllocId_1137_, lean_object* v_inst_1138_, lean_object* v_R_1139_, lean_object* v_a_1140_, lean_object* v_b_1141_, lean_object* v_c_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(v_upperBound_1135_, v_mask_1136_, v_origAllocId_1137_, v_inst_1138_, v_R_1139_, v_a_1140_, v_b_1141_, v_c_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec_ref(v_mask_1136_);
lean_dec(v_upperBound_1135_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object* v_as_1149_, size_t v_sz_1150_, size_t v_i_1151_, lean_object* v_b_1152_){
_start:
{
lean_object* v_a_1155_; uint8_t v___x_1159_; 
v___x_1159_ = lean_usize_dec_lt(v_i_1151_, v_sz_1150_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_b_1152_);
return v___x_1160_;
}
else
{
lean_object* v_a_1161_; 
v_a_1161_ = lean_array_uget_borrowed(v_as_1149_, v_i_1151_);
if (lean_obj_tag(v_a_1161_) == 1)
{
lean_object* v_val_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; 
v_val_1162_ = lean_ctor_get(v_a_1161_, 0);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = 0;
lean_inc(v_val_1162_);
v___x_1165_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1165_, 0, v_val_1162_);
lean_ctor_set(v___x_1165_, 1, v___x_1163_);
lean_ctor_set(v___x_1165_, 2, v_b_1152_);
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*3, v___x_1159_);
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*3 + 1, v___x_1164_);
v_a_1155_ = v___x_1165_;
goto v___jp_1154_;
}
else
{
v_a_1155_ = v_b_1152_;
goto v___jp_1154_;
}
}
v___jp_1154_:
{
size_t v___x_1156_; size_t v___x_1157_; 
v___x_1156_ = ((size_t)1ULL);
v___x_1157_ = lean_usize_add(v_i_1151_, v___x_1156_);
v_i_1151_ = v___x_1157_;
v_b_1152_ = v_a_1155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object* v_as_1166_, lean_object* v_sz_1167_, lean_object* v_i_1168_, lean_object* v_b_1169_, lean_object* v___y_1170_){
_start:
{
size_t v_sz_boxed_1171_; size_t v_i_boxed_1172_; lean_object* v_res_1173_; 
v_sz_boxed_1171_ = lean_unbox_usize(v_sz_1167_);
lean_dec(v_sz_1167_);
v_i_boxed_1172_ = lean_unbox_usize(v_i_1168_);
lean_dec(v_i_1168_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1166_, v_sz_boxed_1171_, v_i_boxed_1172_, v_b_1169_);
lean_dec_ref(v_as_1166_);
return v_res_1173_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_unsigned_to_nat(2u);
v___x_1176_ = lean_mk_empty_array_with_capacity(v___x_1175_);
v___x_1177_ = lean_array_push(v___x_1176_, v___x_1174_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object* v_origAllocId_1178_, lean_object* v_mask_1179_, lean_object* v_resetJpId_1180_, lean_object* v_isSharedId_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_code_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v_code_1195_; size_t v_sz_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_isSharedId_1181_);
v___x_1188_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0);
v___x_1189_ = lean_array_push(v___x_1188_, v___x_1187_);
v_code_1190_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1190_, 0, v_resetJpId_1180_);
lean_ctor_set(v_code_1190_, 1, v___x_1189_);
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = 1;
v___x_1193_ = 0;
v___x_1194_ = lean_box(0);
v_code_1195_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_code_1195_, 0, v_origAllocId_1178_);
lean_ctor_set(v_code_1195_, 1, v___x_1191_);
lean_ctor_set(v_code_1195_, 2, v___x_1194_);
lean_ctor_set(v_code_1195_, 3, v_code_1190_);
lean_ctor_set_uint8(v_code_1195_, sizeof(void*)*4, v___x_1192_);
lean_ctor_set_uint8(v_code_1195_, sizeof(void*)*4 + 1, v___x_1193_);
v_sz_1196_ = lean_array_size(v_mask_1179_);
v___x_1197_ = ((size_t)0ULL);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_mask_1179_, v_sz_1196_, v___x_1197_, v_code_1195_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(lean_object* v_origAllocId_1199_, lean_object* v_mask_1200_, lean_object* v_resetJpId_1201_, lean_object* v_isSharedId_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_1199_, v_mask_1200_, v_resetJpId_1201_, v_isSharedId_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec_ref(v_mask_1200_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(lean_object* v_as_1209_, size_t v_sz_1210_, size_t v_i_1211_, lean_object* v_b_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1209_, v_sz_1210_, v_i_1211_, v_b_1212_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(lean_object* v_as_1219_, lean_object* v_sz_1220_, lean_object* v_i_1221_, lean_object* v_b_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
size_t v_sz_boxed_1228_; size_t v_i_boxed_1229_; lean_object* v_res_1230_; 
v_sz_boxed_1228_ = lean_unbox_usize(v_sz_1220_);
lean_dec(v_sz_1220_);
v_i_boxed_1229_ = lean_unbox_usize(v_i_1221_);
lean_dec(v_i_1221_);
v_res_1230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(v_as_1219_, v_sz_boxed_1228_, v_i_boxed_1229_, v_b_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v_as_1219_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1231_, lean_object* v_args_1232_, lean_object* v_origAllocId_1233_, lean_object* v_resetTokenId_1234_, lean_object* v_a_1235_, lean_object* v_b_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_nat_dec_lt(v_a_1235_, v_upperBound_1231_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec(v_a_1235_);
lean_dec(v_resetTokenId_1234_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_b_1236_);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_array_fget_borrowed(v_args_1232_, v_a_1235_);
v___x_1242_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_origAllocId_1233_, v_a_1235_, v___x_1241_, v___y_1237_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v_a_1245_; uint8_t v___x_1249_; uint8_t v___x_1250_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1249_ = lean_unbox(v_a_1243_);
lean_dec(v_a_1243_);
v___x_1250_ = lean_bool_not(v___x_1249_);
if (v___x_1250_ == 0)
{
v_a_1245_ = v_b_1236_;
goto v___jp_1244_;
}
else
{
lean_object* v___x_1251_; 
lean_inc(v___x_1241_);
lean_inc(v_a_1235_);
lean_inc(v_resetTokenId_1234_);
v___x_1251_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1251_, 0, v_resetTokenId_1234_);
lean_ctor_set(v___x_1251_, 1, v_a_1235_);
lean_ctor_set(v___x_1251_, 2, v___x_1241_);
lean_ctor_set(v___x_1251_, 3, v_b_1236_);
v_a_1245_ = v___x_1251_;
goto v___jp_1244_;
}
v___jp_1244_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_add(v_a_1235_, v___x_1246_);
lean_dec(v_a_1235_);
v_a_1235_ = v___x_1247_;
v_b_1236_ = v_a_1245_;
goto _start;
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_b_1236_);
lean_dec(v_a_1235_);
lean_dec(v_resetTokenId_1234_);
v_a_1252_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1242_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1242_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1260_, lean_object* v_args_1261_, lean_object* v_origAllocId_1262_, lean_object* v_resetTokenId_1263_, lean_object* v_a_1264_, lean_object* v_b_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1260_, v_args_1261_, v_origAllocId_1262_, v_resetTokenId_1263_, v_a_1264_, v_b_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec(v_origAllocId_1262_);
lean_dec_ref(v_args_1261_);
lean_dec(v_upperBound_1260_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(lean_object* v_resetTokenId_1269_, lean_object* v_info_1270_, uint8_t v_update_1271_, lean_object* v_args_1272_, lean_object* v_contJpId_1273_, lean_object* v_origAllocId_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_code_1286_; lean_object* v___x_1287_; 
lean_inc_n(v_resetTokenId_1269_, 2);
v___x_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_resetTokenId_1269_);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_array_get_size(v_args_1272_);
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_mk_empty_array_with_capacity(v___x_1283_);
v___x_1285_ = lean_array_push(v___x_1284_, v___x_1280_);
v_code_1286_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1286_, 0, v_contJpId_1273_);
lean_ctor_set(v_code_1286_, 1, v___x_1285_);
v___x_1287_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v___x_1282_, v_args_1272_, v_origAllocId_1274_, v_resetTokenId_1269_, v___x_1281_, v_code_1286_, v_a_1276_);
if (lean_obj_tag(v___x_1287_) == 0)
{
if (v_update_1271_ == 0)
{
lean_dec(v_resetTokenId_1269_);
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1297_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1297_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1297_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_cidx_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v_cidx_1292_ = lean_ctor_get(v_info_1270_, 1);
lean_inc(v_cidx_1292_);
v___x_1293_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1293_, 0, v_resetTokenId_1269_);
lean_ctor_set(v___x_1293_, 1, v_cidx_1292_);
lean_ctor_set(v___x_1293_, 2, v_a_1288_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1293_);
v___x_1295_ = v___x_1290_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_dec(v_resetTokenId_1269_);
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(lean_object* v_resetTokenId_1298_, lean_object* v_info_1299_, lean_object* v_update_1300_, lean_object* v_args_1301_, lean_object* v_contJpId_1302_, lean_object* v_origAllocId_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
uint8_t v_update_boxed_1309_; lean_object* v_res_1310_; 
v_update_boxed_1309_ = lean_unbox(v_update_1300_);
v_res_1310_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1298_, v_info_1299_, v_update_boxed_1309_, v_args_1301_, v_contJpId_1302_, v_origAllocId_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_origAllocId_1303_);
lean_dec_ref(v_args_1301_);
lean_dec_ref(v_info_1299_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(lean_object* v_upperBound_1311_, lean_object* v_args_1312_, lean_object* v_origAllocId_1313_, lean_object* v_resetTokenId_1314_, lean_object* v_inst_1315_, lean_object* v_R_1316_, lean_object* v_a_1317_, lean_object* v_b_1318_, lean_object* v_c_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1311_, v_args_1312_, v_origAllocId_1313_, v_resetTokenId_1314_, v_a_1317_, v_b_1318_, v___y_1321_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1326_, lean_object* v_args_1327_, lean_object* v_origAllocId_1328_, lean_object* v_resetTokenId_1329_, lean_object* v_inst_1330_, lean_object* v_R_1331_, lean_object* v_a_1332_, lean_object* v_b_1333_, lean_object* v_c_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(v_upperBound_1326_, v_args_1327_, v_origAllocId_1328_, v_resetTokenId_1329_, v_inst_1330_, v_R_1331_, v_a_1332_, v_b_1333_, v_c_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v_origAllocId_1328_);
lean_dec_ref(v_args_1327_);
lean_dec(v_upperBound_1326_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(lean_object* v_decl_1344_, lean_object* v_info_1345_, lean_object* v_args_1346_, lean_object* v_contJpId_1347_, lean_object* v_selfSets_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1));
v___x_1355_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1354_, v_a_1350_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v_type_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v_type_1357_ = lean_ctor_get(v_decl_1344_, 2);
lean_inc_ref(v_type_1357_);
lean_dec_ref(v_decl_1344_);
v___x_1358_ = 1;
v___x_1359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_info_1345_);
lean_ctor_set(v___x_1359_, 1, v_args_1346_);
v___x_1360_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1358_, v_a_1356_, v_type_1357_, v___x_1359_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v_fvarId_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1378_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v_fvarId_1362_ = lean_ctor_get(v_a_1361_, 0);
lean_inc_n(v_fvarId_1362_, 2);
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_fvarId_1362_);
v___x_1364_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_fvarId_1362_, v_selfSets_1348_);
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1378_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1378_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_mk_empty_array_with_capacity(v___x_1369_);
v___x_1371_ = lean_array_push(v___x_1370_, v___x_1363_);
v___x_1372_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_contJpId_1347_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1358_, v_a_1365_, v___x_1372_);
lean_dec(v_a_1365_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_a_1361_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1374_);
v___x_1376_ = v___x_1367_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref(v_selfSets_1348_);
lean_dec(v_contJpId_1347_);
v_a_1379_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1360_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1360_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v_selfSets_1348_);
lean_dec(v_contJpId_1347_);
lean_dec_ref(v_args_1346_);
lean_dec_ref(v_info_1345_);
lean_dec_ref(v_decl_1344_);
v_a_1387_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1355_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1355_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(lean_object* v_decl_1395_, lean_object* v_info_1396_, lean_object* v_args_1397_, lean_object* v_contJpId_1398_, lean_object* v_selfSets_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1395_, v_info_1396_, v_args_1397_, v_contJpId_1398_, v_selfSets_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(lean_object* v_alt_1406_, lean_object* v_f_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___y_1414_; 
switch(lean_obj_tag(v_alt_1406_))
{
case 0:
{
lean_object* v_code_1433_; 
v_code_1433_ = lean_ctor_get(v_alt_1406_, 2);
lean_inc_ref(v_code_1433_);
v___y_1414_ = v_code_1433_;
goto v___jp_1413_;
}
case 1:
{
lean_object* v_code_1434_; 
v_code_1434_ = lean_ctor_get(v_alt_1406_, 1);
lean_inc_ref(v_code_1434_);
v___y_1414_ = v_code_1434_;
goto v___jp_1413_;
}
default: 
{
lean_object* v_code_1435_; 
v_code_1435_ = lean_ctor_get(v_alt_1406_, 0);
lean_inc_ref(v_code_1435_);
v___y_1414_ = v_code_1435_;
goto v___jp_1413_;
}
}
v___jp_1413_:
{
lean_object* v___x_1415_; 
lean_inc(v___y_1411_);
lean_inc_ref(v___y_1410_);
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
v___x_1415_ = lean_apply_6(v_f_1407_, v___y_1414_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, lean_box(0));
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1406_, v_a_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_alt_1406_);
v_a_1425_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1415_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1415_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(lean_object* v_alt_1436_, lean_object* v_f_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1436_, v_f_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(uint8_t v_pu_1444_, lean_object* v_alt_1445_, lean_object* v_f_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1445_, v_f_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(lean_object* v_pu_1453_, lean_object* v_alt_1454_, lean_object* v_f_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v_pu_boxed_1461_; lean_object* v_res_1462_; 
v_pu_boxed_1461_ = lean_unbox(v_pu_1453_);
v_res_1462_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(v_pu_boxed_1461_, v_alt_1454_, v_f_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1462_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0(void){
_start:
{
uint8_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = 1;
v___x_1464_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object* v_msg_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v_toApplicative_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1506_; 
v___x_1471_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_1472_ = l_StateRefT_x27_instMonad___redArg(v___x_1471_);
v_toApplicative_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v___x_1472_, 1);
lean_dec(v_unused_1507_);
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1506_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_toApplicative_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1506_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_toFunctor_1477_; lean_object* v_toSeq_1478_; lean_object* v_toSeqLeft_1479_; lean_object* v_toSeqRight_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1504_; 
v_toFunctor_1477_ = lean_ctor_get(v_toApplicative_1473_, 0);
v_toSeq_1478_ = lean_ctor_get(v_toApplicative_1473_, 2);
v_toSeqLeft_1479_ = lean_ctor_get(v_toApplicative_1473_, 3);
v_toSeqRight_1480_ = lean_ctor_get(v_toApplicative_1473_, 4);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_toApplicative_1473_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; 
v_unused_1505_ = lean_ctor_get(v_toApplicative_1473_, 1);
lean_dec(v_unused_1505_);
v___x_1482_ = v_toApplicative_1473_;
v_isShared_1483_ = v_isSharedCheck_1504_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_toSeqRight_1480_);
lean_inc(v_toSeqLeft_1479_);
lean_inc(v_toSeq_1478_);
lean_inc(v_toFunctor_1477_);
lean_dec(v_toApplicative_1473_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1504_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___f_1484_; lean_object* v___f_1485_; lean_object* v___f_1486_; lean_object* v___f_1487_; lean_object* v___x_1488_; lean_object* v___f_1489_; lean_object* v___f_1490_; lean_object* v___f_1491_; lean_object* v___x_1493_; 
v___f_1484_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_1485_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1477_);
v___f_1486_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1486_, 0, v_toFunctor_1477_);
v___f_1487_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1487_, 0, v_toFunctor_1477_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___f_1486_);
lean_ctor_set(v___x_1488_, 1, v___f_1487_);
v___f_1489_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1489_, 0, v_toSeqRight_1480_);
v___f_1490_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1490_, 0, v_toSeqLeft_1479_);
v___f_1491_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1491_, 0, v_toSeq_1478_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v___f_1489_);
lean_ctor_set(v___x_1482_, 3, v___f_1490_);
lean_ctor_set(v___x_1482_, 2, v___f_1491_);
lean_ctor_set(v___x_1482_, 1, v___f_1484_);
lean_ctor_set(v___x_1482_, 0, v___x_1488_);
v___x_1493_ = v___x_1482_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v___f_1484_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v___f_1491_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v___f_1490_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v___f_1489_);
v___x_1493_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___f_1485_);
lean_ctor_set(v___x_1475_, 0, v___x_1493_);
v___x_1495_ = v___x_1475_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___f_1485_);
v___x_1495_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___f_1499_; lean_object* v___x_6925__overap_1500_; lean_object* v___x_1501_; 
v___x_1496_ = l_StateRefT_x27_instMonad___redArg(v___x_1495_);
v___x_1497_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0);
v___x_1498_ = l_instInhabitedOfMonad___redArg(v___x_1496_, v___x_1497_);
v___f_1499_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1499_, 0, v___x_1498_);
v___x_6925__overap_1500_ = lean_panic_fn_borrowed(v___f_1499_, v_msg_1465_);
lean_dec_ref(v___f_1499_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
v___x_1501_ = lean_apply_5(v___x_6925__overap_1500_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, lean_box(0));
return v___x_1501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object* v_msg_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v_msg_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1514_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_box(0);
v___x_1522_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3));
v___x_1523_ = l_Lean_Expr_const___override(v___x_1522_, v___x_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object* v_resetTokenId_1524_, lean_object* v_origAllocId_1525_, lean_object* v_isSharedId_1526_, lean_object* v_resultType_1527_, lean_object* v_x_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(v_resetTokenId_1524_, v_origAllocId_1525_, v_isSharedId_1526_, v_resultType_1527_, v_x_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object* v_resetTokenId_1535_, lean_object* v_origAllocId_1536_, lean_object* v_isSharedId_1537_, lean_object* v_resultType_1538_, lean_object* v_i_1539_, lean_object* v_as_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = lean_array_get_size(v_as_1540_);
v___x_1547_ = lean_nat_dec_lt(v_i_1539_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
lean_dec(v_i_1539_);
lean_dec_ref(v_resultType_1538_);
lean_dec(v_isSharedId_1537_);
lean_dec(v_origAllocId_1536_);
lean_dec(v_resetTokenId_1535_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_as_1540_);
return v___x_1548_;
}
else
{
lean_object* v___f_1549_; lean_object* v_a_1550_; lean_object* v___x_1551_; 
lean_inc_ref(v_resultType_1538_);
lean_inc(v_isSharedId_1537_);
lean_inc(v_origAllocId_1536_);
lean_inc(v_resetTokenId_1535_);
v___f_1549_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1549_, 0, v_resetTokenId_1535_);
lean_closure_set(v___f_1549_, 1, v_origAllocId_1536_);
lean_closure_set(v___f_1549_, 2, v_isSharedId_1537_);
lean_closure_set(v___f_1549_, 3, v_resultType_1538_);
v_a_1550_ = lean_array_fget_borrowed(v_as_1540_, v_i_1539_);
lean_inc(v_a_1550_);
v___x_1551_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_1550_, v___f_1549_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; size_t v___x_1553_; size_t v___x_1554_; uint8_t v___x_1555_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = lean_ptr_addr(v_a_1550_);
v___x_1554_ = lean_ptr_addr(v_a_1552_);
v___x_1555_ = lean_usize_dec_eq(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_add(v_i_1539_, v___x_1556_);
v___x_1558_ = lean_array_fset(v_as_1540_, v_i_1539_, v_a_1552_);
lean_dec(v_i_1539_);
v_i_1539_ = v___x_1557_;
v_as_1540_ = v___x_1558_;
goto _start;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_a_1552_);
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_nat_add(v_i_1539_, v___x_1560_);
lean_dec(v_i_1539_);
v_i_1539_ = v___x_1561_;
goto _start;
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v_as_1540_);
lean_dec(v_i_1539_);
lean_dec_ref(v_resultType_1538_);
lean_dec(v_isSharedId_1537_);
lean_dec(v_origAllocId_1536_);
lean_dec(v_resetTokenId_1535_);
v_a_1563_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1551_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1551_);
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
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1573_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6));
v___x_1574_ = lean_unsigned_to_nat(6u);
v___x_1575_ = lean_unsigned_to_nat(208u);
v___x_1576_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5));
v___x_1577_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_1578_ = l_mkPanicMessageWithDecl(v___x_1577_, v___x_1576_, v___x_1575_, v___x_1574_, v___x_1573_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object* v_resetTokenId_1579_, lean_object* v_code_1580_, lean_object* v_origAllocId_1581_, lean_object* v_isSharedId_1582_, lean_object* v_currentRetType_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
switch(lean_obj_tag(v_code_1580_))
{
case 0:
{
lean_object* v_decl_1589_; lean_object* v_value_1590_; 
v_decl_1589_ = lean_ctor_get(v_code_1580_, 0);
v_value_1590_ = lean_ctor_get(v_decl_1589_, 3);
lean_inc(v_value_1590_);
if (lean_obj_tag(v_value_1590_) == 12)
{
lean_object* v_k_1591_; lean_object* v_fvarId_1592_; lean_object* v_binderName_1593_; lean_object* v_type_1594_; lean_object* v_var_1595_; lean_object* v_i_1596_; uint8_t v_updateHeader_1597_; lean_object* v_args_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1714_; 
v_k_1591_ = lean_ctor_get(v_code_1580_, 1);
v_fvarId_1592_ = lean_ctor_get(v_decl_1589_, 0);
v_binderName_1593_ = lean_ctor_get(v_decl_1589_, 1);
v_type_1594_ = lean_ctor_get(v_decl_1589_, 2);
v_var_1595_ = lean_ctor_get(v_value_1590_, 0);
v_i_1596_ = lean_ctor_get(v_value_1590_, 1);
v_updateHeader_1597_ = lean_ctor_get_uint8(v_value_1590_, sizeof(void*)*3);
v_args_1598_ = lean_ctor_get(v_value_1590_, 2);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_value_1590_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1600_ = v_value_1590_;
v_isShared_1601_ = v_isSharedCheck_1714_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_args_1598_);
lean_inc(v_i_1596_);
lean_inc(v_var_1595_);
lean_dec(v_value_1590_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1714_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
uint8_t v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1579_, v_var_1595_);
lean_dec(v_var_1595_);
v___x_1603_ = lean_bool_not(v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1687_; 
lean_inc_ref(v_k_1591_);
lean_inc_ref(v_decl_1589_);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; lean_object* v_unused_1689_; 
v_unused_1688_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_1689_);
v___x_1605_ = v_code_1580_;
v_isShared_1606_ = v_isSharedCheck_1687_;
goto v_resetjp_1604_;
}
else
{
lean_dec(v_code_1580_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1687_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; 
v___x_1607_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_fvarId_1592_, v_k_1591_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v_fst_1609_; lean_object* v_snd_1610_; lean_object* v___x_1611_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v_fst_1609_ = lean_ctor_get(v_a_1608_, 0);
lean_inc(v_fst_1609_);
v_snd_1610_ = lean_ctor_get(v_a_1608_, 1);
lean_inc(v_snd_1610_);
lean_dec(v_a_1608_);
v___x_1611_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_origAllocId_1581_, v_fst_1609_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_fst_1609_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v_fst_1613_; lean_object* v_snd_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v_fst_1613_ = lean_ctor_get(v_a_1612_, 0);
lean_inc(v_fst_1613_);
v_snd_1614_ = lean_ctor_get(v_a_1612_, 1);
lean_inc(v_snd_1614_);
lean_dec(v_a_1612_);
v___x_1615_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1));
v___x_1616_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1615_, v_a_1585_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = 1;
v___x_1619_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1618_, v_snd_1614_, v_snd_1610_);
lean_dec(v_snd_1614_);
lean_inc_ref(v_type_1594_);
lean_inc(v_binderName_1593_);
lean_inc(v_fvarId_1592_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 0);
lean_ctor_set(v___x_1600_, 2, v_type_1594_);
lean_ctor_set(v___x_1600_, 1, v_binderName_1593_);
lean_ctor_set(v___x_1600_, 0, v_fvarId_1592_);
v___x_1621_ = v___x_1600_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_fvarId_1592_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_binderName_1593_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_type_1594_);
v___x_1621_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*3, v___x_1603_);
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = lean_mk_empty_array_with_capacity(v___x_1622_);
v___x_1624_ = lean_array_push(v___x_1623_, v___x_1621_);
lean_inc_ref(v_currentRetType_1583_);
v___x_1625_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_1618_, v_a_1617_, v_currentRetType_1583_, v___x_1624_, v___x_1619_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v_fvarId_1627_; lean_object* v___x_1628_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v_fvarId_1627_ = lean_ctor_get(v_a_1626_, 0);
lean_inc(v_fvarId_1627_);
lean_inc_ref(v_args_1598_);
lean_inc_ref(v_i_1596_);
lean_inc_ref(v_decl_1589_);
v___x_1628_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1589_, v_i_1596_, v_args_1598_, v_fvarId_1627_, v_fst_1613_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
lean_inc(v_fvarId_1627_);
v___x_1630_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1579_, v_i_1596_, v_updateHeader_1597_, v_args_1598_, v_fvarId_1627_, v_origAllocId_1581_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_origAllocId_1581_);
lean_dec_ref(v_args_1598_);
lean_dec_ref(v_i_1596_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_1618_, v_decl_1589_, v_a_1585_);
lean_dec_ref(v_decl_1589_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec_ref_known(v___x_1632_, 1);
v___x_1633_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_1634_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_isSharedId_1582_, v___x_1633_, v_currentRetType_1583_, v_a_1629_, v_a_1631_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1645_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1645_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1645_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set_tag(v___x_1605_, 2);
lean_ctor_set(v___x_1605_, 1, v_a_1635_);
lean_ctor_set(v___x_1605_, 0, v_a_1626_);
v___x_1640_ = v___x_1605_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1626_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1642_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1640_);
v___x_1642_ = v___x_1637_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_dec(v_a_1626_);
lean_del_object(v___x_1605_);
return v___x_1634_;
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_a_1631_);
lean_dec(v_a_1629_);
lean_dec(v_a_1626_);
lean_del_object(v___x_1605_);
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
v_a_1646_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1632_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1632_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_dec(v_a_1629_);
lean_dec(v_a_1626_);
lean_del_object(v___x_1605_);
lean_dec_ref(v_decl_1589_);
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
return v___x_1630_;
}
}
else
{
lean_dec(v_a_1626_);
lean_del_object(v___x_1605_);
lean_dec_ref(v_args_1598_);
lean_dec_ref(v_i_1596_);
lean_dec_ref(v_decl_1589_);
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
lean_dec(v_origAllocId_1581_);
lean_dec(v_resetTokenId_1579_);
return v___x_1628_;
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_fst_1613_);
lean_del_object(v___x_1605_);
lean_dec_ref(v_args_1598_);
lean_dec_ref(v_i_1596_);
lean_dec_ref(v_decl_1589_);
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
lean_dec(v_origAllocId_1581_);
lean_dec(v_resetTokenId_1579_);
v_a_1654_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1625_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1625_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_snd_1614_);
lean_dec(v_fst_1613_);
lean_dec(v_snd_1610_);
lean_del_object(v___x_1605_);
lean_del_object(v___x_1600_);
lean_dec_ref(v_args_1598_);
lean_dec_ref(v_i_1596_);
lean_dec_ref(v_decl_1589_);
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
lean_dec(v_origAllocId_1581_);
lean_dec(v_resetTokenId_1579_);
v_a_1663_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1616_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1616_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_snd_1610_);
lean_del_object(v___x_1605_);
lean_del_object(v___x_1600_);
lean_dec_ref(v_args_1598_);
lean_dec_ref(v_i_1596_);
lean_dec_ref(v_decl_1589_);
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
lean_dec(v_origAllocId_1581_);
lean_dec(v_resetTokenId_1579_);
v_a_1671_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1611_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1611_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_del_object(v___x_1605_);
lean_del_object(v___x_1600_);
lean_dec_ref(v_args_1598_);
lean_dec_ref(v_i_1596_);
lean_dec_ref(v_decl_1589_);
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
lean_dec(v_origAllocId_1581_);
lean_dec(v_resetTokenId_1579_);
v_a_1679_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1607_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1607_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
else
{
lean_object* v___x_1690_; 
lean_del_object(v___x_1600_);
lean_dec_ref(v_args_1598_);
lean_dec_ref(v_i_1596_);
lean_inc_ref(v_k_1591_);
v___x_1690_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_k_1591_, v_origAllocId_1581_, v_isSharedId_1582_, v_currentRetType_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1713_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1713_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1713_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
size_t v___x_1695_; size_t v___x_1696_; uint8_t v___x_1697_; 
v___x_1695_ = lean_ptr_addr(v_k_1591_);
v___x_1696_ = lean_ptr_addr(v_a_1691_);
v___x_1697_ = lean_usize_dec_eq(v___x_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1707_; 
lean_inc_ref(v_decl_1589_);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; lean_object* v_unused_1709_; 
v_unused_1708_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_1709_);
v___x_1699_ = v_code_1580_;
v_isShared_1700_ = v_isSharedCheck_1707_;
goto v_resetjp_1698_;
}
else
{
lean_dec(v_code_1580_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1707_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v_a_1691_);
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_decl_1589_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_a_1691_);
v___x_1702_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1704_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1702_);
v___x_1704_ = v___x_1693_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v___x_1711_; 
lean_dec(v_a_1691_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v_code_1580_);
v___x_1711_ = v___x_1693_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_code_1580_);
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
lean_dec_ref_known(v_code_1580_, 2);
return v___x_1690_;
}
}
}
}
else
{
lean_object* v_k_1715_; lean_object* v___x_1716_; 
lean_dec(v_value_1590_);
v_k_1715_ = lean_ctor_get(v_code_1580_, 1);
lean_inc_ref(v_k_1715_);
v___x_1716_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_k_1715_, v_origAllocId_1581_, v_isSharedId_1582_, v_currentRetType_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1739_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1739_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1739_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
size_t v___x_1721_; size_t v___x_1722_; uint8_t v___x_1723_; 
v___x_1721_ = lean_ptr_addr(v_k_1715_);
v___x_1722_ = lean_ptr_addr(v_a_1717_);
v___x_1723_ = lean_usize_dec_eq(v___x_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1733_; 
lean_inc_ref(v_decl_1589_);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; lean_object* v_unused_1735_; 
v_unused_1734_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_1735_);
v___x_1725_ = v_code_1580_;
v_isShared_1726_ = v_isSharedCheck_1733_;
goto v_resetjp_1724_;
}
else
{
lean_dec(v_code_1580_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1733_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v_a_1717_);
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_decl_1589_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_a_1717_);
v___x_1728_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1730_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1728_);
v___x_1730_ = v___x_1719_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v___x_1737_; 
lean_dec(v_a_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v_code_1580_);
v___x_1737_ = v___x_1719_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_code_1580_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1580_, 2);
return v___x_1716_;
}
}
}
case 2:
{
lean_object* v_decl_1740_; lean_object* v_k_1741_; lean_object* v_params_1742_; lean_object* v_type_1743_; lean_object* v_value_1744_; lean_object* v___x_1745_; 
v_decl_1740_ = lean_ctor_get(v_code_1580_, 0);
v_k_1741_ = lean_ctor_get(v_code_1580_, 1);
v_params_1742_ = lean_ctor_get(v_decl_1740_, 2);
v_type_1743_ = lean_ctor_get(v_decl_1740_, 3);
v_value_1744_ = lean_ctor_get(v_decl_1740_, 4);
lean_inc_ref(v_type_1743_);
lean_inc(v_isSharedId_1582_);
lean_inc(v_origAllocId_1581_);
lean_inc_ref(v_value_1744_);
lean_inc(v_resetTokenId_1579_);
v___x_1745_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_value_1744_, v_origAllocId_1581_, v_isSharedId_1582_, v_type_1743_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1747_ = 1;
lean_inc_ref(v_params_1742_);
lean_inc_ref(v_type_1743_);
lean_inc_ref(v_decl_1740_);
v___x_1748_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1747_, v_decl_1740_, v_type_1743_, v_params_1742_, v_a_1746_, v_a_1585_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
lean_inc_ref(v_k_1741_);
v___x_1750_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_k_1741_, v_origAllocId_1581_, v_isSharedId_1582_, v_currentRetType_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1778_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1778_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1778_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
uint8_t v___y_1756_; size_t v___x_1772_; size_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = lean_ptr_addr(v_k_1741_);
v___x_1773_ = lean_ptr_addr(v_a_1751_);
v___x_1774_ = lean_usize_dec_eq(v___x_1772_, v___x_1773_);
if (v___x_1774_ == 0)
{
v___y_1756_ = v___x_1774_;
goto v___jp_1755_;
}
else
{
size_t v___x_1775_; size_t v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_ptr_addr(v_decl_1740_);
v___x_1776_ = lean_ptr_addr(v_a_1749_);
v___x_1777_ = lean_usize_dec_eq(v___x_1775_, v___x_1776_);
v___y_1756_ = v___x_1777_;
goto v___jp_1755_;
}
v___jp_1755_:
{
if (v___y_1756_ == 0)
{
lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1766_; 
v_isSharedCheck_1766_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; lean_object* v_unused_1768_; 
v_unused_1767_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_1767_);
v_unused_1768_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_1768_);
v___x_1758_ = v_code_1580_;
v_isShared_1759_ = v_isSharedCheck_1766_;
goto v_resetjp_1757_;
}
else
{
lean_dec(v_code_1580_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1766_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 1, v_a_1751_);
lean_ctor_set(v___x_1758_, 0, v_a_1749_);
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1749_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_a_1751_);
v___x_1761_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1763_; 
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1761_);
v___x_1763_ = v___x_1753_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
else
{
lean_object* v___x_1770_; 
lean_dec(v_a_1751_);
lean_dec(v_a_1749_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v_code_1580_);
v___x_1770_ = v___x_1753_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_code_1580_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
else
{
lean_dec(v_a_1749_);
lean_dec_ref_known(v_code_1580_, 2);
return v___x_1750_;
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref_known(v_code_1580_, 2);
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
lean_dec(v_origAllocId_1581_);
lean_dec(v_resetTokenId_1579_);
v_a_1779_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1748_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1748_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1580_, 2);
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
lean_dec(v_origAllocId_1581_);
lean_dec(v_resetTokenId_1579_);
return v___x_1745_;
}
}
case 4:
{
lean_object* v_cases_1787_; lean_object* v_typeName_1788_; lean_object* v_resultType_1789_; lean_object* v_discr_1790_; lean_object* v_alts_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v_currentRetType_1583_);
v_cases_1787_ = lean_ctor_get(v_code_1580_, 0);
lean_inc_ref(v_cases_1787_);
v_typeName_1788_ = lean_ctor_get(v_cases_1787_, 0);
v_resultType_1789_ = lean_ctor_get(v_cases_1787_, 1);
v_discr_1790_ = lean_ctor_get(v_cases_1787_, 2);
v_alts_1791_ = lean_ctor_get(v_cases_1787_, 3);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_cases_1787_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1793_ = v_cases_1787_;
v_isShared_1794_ = v_isSharedCheck_1830_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_alts_1791_);
lean_inc(v_discr_1790_);
lean_inc(v_resultType_1789_);
lean_inc(v_typeName_1788_);
lean_dec(v_cases_1787_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1830_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1791_);
lean_inc_ref(v_resultType_1789_);
v___x_1796_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_1579_, v_origAllocId_1581_, v_isSharedId_1582_, v_resultType_1789_, v___x_1795_, v_alts_1791_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1821_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1821_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1821_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
size_t v___x_1801_; size_t v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = lean_ptr_addr(v_alts_1791_);
lean_dec_ref(v_alts_1791_);
v___x_1802_ = lean_ptr_addr(v_a_1797_);
v___x_1803_ = lean_usize_dec_eq(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1816_; 
v_isSharedCheck_1816_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_1817_);
v___x_1805_ = v_code_1580_;
v_isShared_1806_ = v_isSharedCheck_1816_;
goto v_resetjp_1804_;
}
else
{
lean_dec(v_code_1580_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1816_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 3, v_a_1797_);
v___x_1808_ = v___x_1793_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_typeName_1788_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_resultType_1789_);
lean_ctor_set(v_reuseFailAlloc_1815_, 2, v_discr_1790_);
lean_ctor_set(v_reuseFailAlloc_1815_, 3, v_a_1797_);
v___x_1808_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1808_);
v___x_1810_ = v___x_1805_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1810_);
v___x_1812_ = v___x_1799_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
else
{
lean_object* v___x_1819_; 
lean_dec(v_a_1797_);
lean_del_object(v___x_1793_);
lean_dec(v_discr_1790_);
lean_dec_ref(v_resultType_1789_);
lean_dec(v_typeName_1788_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v_code_1580_);
v___x_1819_ = v___x_1799_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_code_1580_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_del_object(v___x_1793_);
lean_dec_ref(v_alts_1791_);
lean_dec(v_discr_1790_);
lean_dec_ref(v_resultType_1789_);
lean_dec(v_typeName_1788_);
lean_dec_ref_known(v_code_1580_, 1);
v_a_1822_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1796_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1796_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1831_; lean_object* v_i_1832_; lean_object* v_y_1833_; lean_object* v_k_1834_; lean_object* v___x_1835_; 
v_fvarId_1831_ = lean_ctor_get(v_code_1580_, 0);
v_i_1832_ = lean_ctor_get(v_code_1580_, 1);
v_y_1833_ = lean_ctor_get(v_code_1580_, 2);
v_k_1834_ = lean_ctor_get(v_code_1580_, 3);
lean_inc_ref(v_k_1834_);
v___x_1835_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_k_1834_, v_origAllocId_1581_, v_isSharedId_1582_, v_currentRetType_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1860_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1860_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1860_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
size_t v___x_1840_; size_t v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = lean_ptr_addr(v_k_1834_);
v___x_1841_ = lean_ptr_addr(v_a_1836_);
v___x_1842_ = lean_usize_dec_eq(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1852_; 
lean_inc(v_y_1833_);
lean_inc(v_i_1832_);
lean_inc(v_fvarId_1831_);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; 
v_unused_1853_ = lean_ctor_get(v_code_1580_, 3);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_code_1580_, 2);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_1856_);
v___x_1844_ = v_code_1580_;
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
else
{
lean_dec(v_code_1580_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 3, v_a_1836_);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_fvarId_1831_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_i_1832_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_y_1833_);
lean_ctor_set(v_reuseFailAlloc_1851_, 3, v_a_1836_);
v___x_1847_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1847_);
v___x_1849_ = v___x_1838_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v___x_1858_; 
lean_dec(v_a_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v_code_1580_);
v___x_1858_ = v___x_1838_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_code_1580_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1580_, 4);
return v___x_1835_;
}
}
case 8:
{
lean_object* v_fvarId_1861_; lean_object* v_i_1862_; lean_object* v_y_1863_; lean_object* v_k_1864_; lean_object* v___x_1865_; 
v_fvarId_1861_ = lean_ctor_get(v_code_1580_, 0);
v_i_1862_ = lean_ctor_get(v_code_1580_, 1);
v_y_1863_ = lean_ctor_get(v_code_1580_, 2);
v_k_1864_ = lean_ctor_get(v_code_1580_, 3);
lean_inc_ref(v_k_1864_);
v___x_1865_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_k_1864_, v_origAllocId_1581_, v_isSharedId_1582_, v_currentRetType_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1890_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1890_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1890_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
size_t v___x_1870_; size_t v___x_1871_; uint8_t v___x_1872_; 
v___x_1870_ = lean_ptr_addr(v_k_1864_);
v___x_1871_ = lean_ptr_addr(v_a_1866_);
v___x_1872_ = lean_usize_dec_eq(v___x_1870_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1882_; 
lean_inc(v_y_1863_);
lean_inc(v_i_1862_);
lean_inc(v_fvarId_1861_);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; lean_object* v_unused_1884_; lean_object* v_unused_1885_; lean_object* v_unused_1886_; 
v_unused_1883_ = lean_ctor_get(v_code_1580_, 3);
lean_dec(v_unused_1883_);
v_unused_1884_ = lean_ctor_get(v_code_1580_, 2);
lean_dec(v_unused_1884_);
v_unused_1885_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_1885_);
v_unused_1886_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_1886_);
v___x_1874_ = v_code_1580_;
v_isShared_1875_ = v_isSharedCheck_1882_;
goto v_resetjp_1873_;
}
else
{
lean_dec(v_code_1580_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1882_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 3, v_a_1866_);
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_fvarId_1861_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_i_1862_);
lean_ctor_set(v_reuseFailAlloc_1881_, 2, v_y_1863_);
lean_ctor_set(v_reuseFailAlloc_1881_, 3, v_a_1866_);
v___x_1877_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1879_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1877_);
v___x_1879_ = v___x_1868_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v___x_1888_; 
lean_dec(v_a_1866_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v_code_1580_);
v___x_1888_ = v___x_1868_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_code_1580_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1580_, 4);
return v___x_1865_;
}
}
case 9:
{
lean_object* v_fvarId_1891_; lean_object* v_i_1892_; lean_object* v_offset_1893_; lean_object* v_y_1894_; lean_object* v_ty_1895_; lean_object* v_k_1896_; lean_object* v___x_1897_; 
v_fvarId_1891_ = lean_ctor_get(v_code_1580_, 0);
v_i_1892_ = lean_ctor_get(v_code_1580_, 1);
v_offset_1893_ = lean_ctor_get(v_code_1580_, 2);
v_y_1894_ = lean_ctor_get(v_code_1580_, 3);
v_ty_1895_ = lean_ctor_get(v_code_1580_, 4);
v_k_1896_ = lean_ctor_get(v_code_1580_, 5);
lean_inc_ref(v_k_1896_);
v___x_1897_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_k_1896_, v_origAllocId_1581_, v_isSharedId_1582_, v_currentRetType_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1924_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1924_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1924_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
size_t v___x_1902_; size_t v___x_1903_; uint8_t v___x_1904_; 
v___x_1902_ = lean_ptr_addr(v_k_1896_);
v___x_1903_ = lean_ptr_addr(v_a_1898_);
v___x_1904_ = lean_usize_dec_eq(v___x_1902_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1914_; 
lean_inc_ref(v_ty_1895_);
lean_inc(v_y_1894_);
lean_inc(v_offset_1893_);
lean_inc(v_i_1892_);
lean_inc(v_fvarId_1891_);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; lean_object* v_unused_1916_; lean_object* v_unused_1917_; lean_object* v_unused_1918_; lean_object* v_unused_1919_; lean_object* v_unused_1920_; 
v_unused_1915_ = lean_ctor_get(v_code_1580_, 5);
lean_dec(v_unused_1915_);
v_unused_1916_ = lean_ctor_get(v_code_1580_, 4);
lean_dec(v_unused_1916_);
v_unused_1917_ = lean_ctor_get(v_code_1580_, 3);
lean_dec(v_unused_1917_);
v_unused_1918_ = lean_ctor_get(v_code_1580_, 2);
lean_dec(v_unused_1918_);
v_unused_1919_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_1919_);
v_unused_1920_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_1920_);
v___x_1906_ = v_code_1580_;
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
else
{
lean_dec(v_code_1580_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 5, v_a_1898_);
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_fvarId_1891_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_i_1892_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_offset_1893_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_y_1894_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v_ty_1895_);
lean_ctor_set(v_reuseFailAlloc_1913_, 5, v_a_1898_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1911_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1909_);
v___x_1911_ = v___x_1900_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v___x_1922_; 
lean_dec(v_a_1898_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v_code_1580_);
v___x_1922_ = v___x_1900_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_code_1580_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1580_, 6);
return v___x_1897_;
}
}
case 10:
{
lean_object* v_fvarId_1925_; lean_object* v_cidx_1926_; lean_object* v_k_1927_; lean_object* v___x_1928_; 
v_fvarId_1925_ = lean_ctor_get(v_code_1580_, 0);
v_cidx_1926_ = lean_ctor_get(v_code_1580_, 1);
v_k_1927_ = lean_ctor_get(v_code_1580_, 2);
lean_inc_ref(v_k_1927_);
v___x_1928_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_k_1927_, v_origAllocId_1581_, v_isSharedId_1582_, v_currentRetType_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1952_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1952_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1952_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
size_t v___x_1933_; size_t v___x_1934_; uint8_t v___x_1935_; 
v___x_1933_ = lean_ptr_addr(v_k_1927_);
v___x_1934_ = lean_ptr_addr(v_a_1929_);
v___x_1935_ = lean_usize_dec_eq(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1945_; 
lean_inc(v_cidx_1926_);
lean_inc(v_fvarId_1925_);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; lean_object* v_unused_1947_; lean_object* v_unused_1948_; 
v_unused_1946_ = lean_ctor_get(v_code_1580_, 2);
lean_dec(v_unused_1946_);
v_unused_1947_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_1947_);
v_unused_1948_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_1948_);
v___x_1937_ = v_code_1580_;
v_isShared_1938_ = v_isSharedCheck_1945_;
goto v_resetjp_1936_;
}
else
{
lean_dec(v_code_1580_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1945_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 2, v_a_1929_);
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_fvarId_1925_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_cidx_1926_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_a_1929_);
v___x_1940_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1942_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1940_);
v___x_1942_ = v___x_1931_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v___x_1950_; 
lean_dec(v_a_1929_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v_code_1580_);
v___x_1950_ = v___x_1931_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_code_1580_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1580_, 3);
return v___x_1928_;
}
}
case 11:
{
lean_object* v_fvarId_1953_; lean_object* v_n_1954_; uint8_t v_check_1955_; uint8_t v_persistent_1956_; lean_object* v_k_1957_; lean_object* v___x_1958_; 
v_fvarId_1953_ = lean_ctor_get(v_code_1580_, 0);
v_n_1954_ = lean_ctor_get(v_code_1580_, 1);
v_check_1955_ = lean_ctor_get_uint8(v_code_1580_, sizeof(void*)*3);
v_persistent_1956_ = lean_ctor_get_uint8(v_code_1580_, sizeof(void*)*3 + 1);
v_k_1957_ = lean_ctor_get(v_code_1580_, 2);
lean_inc_ref(v_k_1957_);
v___x_1958_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_k_1957_, v_origAllocId_1581_, v_isSharedId_1582_, v_currentRetType_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1982_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1982_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1982_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
size_t v___x_1963_; size_t v___x_1964_; uint8_t v___x_1965_; 
v___x_1963_ = lean_ptr_addr(v_k_1957_);
v___x_1964_ = lean_ptr_addr(v_a_1959_);
v___x_1965_ = lean_usize_dec_eq(v___x_1963_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1975_; 
lean_inc(v_n_1954_);
lean_inc(v_fvarId_1953_);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; lean_object* v_unused_1977_; lean_object* v_unused_1978_; 
v_unused_1976_ = lean_ctor_get(v_code_1580_, 2);
lean_dec(v_unused_1976_);
v_unused_1977_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_1977_);
v_unused_1978_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_1978_);
v___x_1967_ = v_code_1580_;
v_isShared_1968_ = v_isSharedCheck_1975_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v_code_1580_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1975_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 2, v_a_1959_);
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_fvarId_1953_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_n_1954_);
lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_a_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1974_, sizeof(void*)*3, v_check_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1974_, sizeof(void*)*3 + 1, v_persistent_1956_);
v___x_1970_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1972_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1970_);
v___x_1972_ = v___x_1961_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v___x_1980_; 
lean_dec(v_a_1959_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v_code_1580_);
v___x_1980_ = v___x_1961_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_code_1580_);
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
lean_dec_ref_known(v_code_1580_, 3);
return v___x_1958_;
}
}
case 12:
{
lean_object* v_fvarId_1983_; lean_object* v_n_1984_; uint8_t v_check_1985_; uint8_t v_persistent_1986_; lean_object* v_objs_x3f_1987_; lean_object* v_k_1988_; uint8_t v___x_1989_; 
v_fvarId_1983_ = lean_ctor_get(v_code_1580_, 0);
v_n_1984_ = lean_ctor_get(v_code_1580_, 1);
v_check_1985_ = lean_ctor_get_uint8(v_code_1580_, sizeof(void*)*4);
v_persistent_1986_ = lean_ctor_get_uint8(v_code_1580_, sizeof(void*)*4 + 1);
v_objs_x3f_1987_ = lean_ctor_get(v_code_1580_, 2);
v_k_1988_ = lean_ctor_get(v_code_1580_, 3);
v___x_1989_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1579_, v_fvarId_1983_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
lean_inc_ref(v_k_1988_);
v___x_1990_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_k_1988_, v_origAllocId_1581_, v_isSharedId_1582_, v_currentRetType_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2015_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2015_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2015_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
size_t v___x_1995_; size_t v___x_1996_; uint8_t v___x_1997_; 
v___x_1995_ = lean_ptr_addr(v_k_1988_);
v___x_1996_ = lean_ptr_addr(v_a_1991_);
v___x_1997_ = lean_usize_dec_eq(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2007_; 
lean_inc(v_objs_x3f_1987_);
lean_inc(v_n_1984_);
lean_inc(v_fvarId_1983_);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; lean_object* v_unused_2009_; lean_object* v_unused_2010_; lean_object* v_unused_2011_; 
v_unused_2008_ = lean_ctor_get(v_code_1580_, 3);
lean_dec(v_unused_2008_);
v_unused_2009_ = lean_ctor_get(v_code_1580_, 2);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_2011_);
v___x_1999_ = v_code_1580_;
v_isShared_2000_ = v_isSharedCheck_2007_;
goto v_resetjp_1998_;
}
else
{
lean_dec(v_code_1580_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2007_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 3, v_a_1991_);
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_fvarId_1983_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_n_1984_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_objs_x3f_1987_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_a_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*4, v_check_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*4 + 1, v_persistent_1986_);
v___x_2002_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2004_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2002_);
v___x_2004_ = v___x_1993_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v___x_2013_; 
lean_dec(v_a_1991_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v_code_1580_);
v___x_2013_ = v___x_1993_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_code_1580_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1580_, 4);
return v___x_1990_;
}
}
else
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
lean_inc_ref(v_k_1988_);
lean_inc(v_n_1984_);
lean_dec_ref_known(v_code_1580_, 4);
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
lean_dec(v_origAllocId_1581_);
v___x_2016_ = lean_unsigned_to_nat(1u);
v___x_2017_ = lean_nat_dec_eq(v_n_1984_, v___x_2016_);
lean_dec(v_n_1984_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec_ref(v_k_1988_);
lean_dec(v_resetTokenId_1579_);
v___x_2018_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7);
v___x_2019_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v___x_2018_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_2020_, 0, v_resetTokenId_1579_);
lean_ctor_set(v___x_2020_, 1, v_k_1988_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
}
case 13:
{
lean_object* v_fvarId_2022_; lean_object* v_k_2023_; lean_object* v___x_2024_; 
v_fvarId_2022_ = lean_ctor_get(v_code_1580_, 0);
v_k_2023_ = lean_ctor_get(v_code_1580_, 1);
lean_inc_ref(v_k_2023_);
v___x_2024_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1579_, v_k_2023_, v_origAllocId_1581_, v_isSharedId_1582_, v_currentRetType_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2047_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2047_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2047_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
size_t v___x_2029_; size_t v___x_2030_; uint8_t v___x_2031_; 
v___x_2029_ = lean_ptr_addr(v_k_2023_);
v___x_2030_ = lean_ptr_addr(v_a_2025_);
v___x_2031_ = lean_usize_dec_eq(v___x_2029_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2041_; 
lean_inc(v_fvarId_2022_);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_code_1580_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; lean_object* v_unused_2043_; 
v_unused_2042_ = lean_ctor_get(v_code_1580_, 1);
lean_dec(v_unused_2042_);
v_unused_2043_ = lean_ctor_get(v_code_1580_, 0);
lean_dec(v_unused_2043_);
v___x_2033_ = v_code_1580_;
v_isShared_2034_ = v_isSharedCheck_2041_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v_code_1580_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2041_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v_a_2025_);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_fvarId_2022_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_a_2025_);
v___x_2036_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2038_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2036_);
v___x_2038_ = v___x_2027_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_object* v___x_2045_; 
lean_dec(v_a_2025_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v_code_1580_);
v___x_2045_ = v___x_2027_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_code_1580_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1580_, 2);
return v___x_2024_;
}
}
default: 
{
lean_object* v___x_2048_; 
lean_dec_ref(v_currentRetType_1583_);
lean_dec(v_isSharedId_1582_);
lean_dec(v_origAllocId_1581_);
lean_dec(v_resetTokenId_1579_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_code_1580_);
return v___x_2048_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object* v_resetTokenId_2049_, lean_object* v_origAllocId_2050_, lean_object* v_isSharedId_2051_, lean_object* v_resultType_2052_, lean_object* v_x_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2049_, v_x_2053_, v_origAllocId_2050_, v_isSharedId_2051_, v_resultType_2052_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object* v_resetTokenId_2060_, lean_object* v_origAllocId_2061_, lean_object* v_isSharedId_2062_, lean_object* v_resultType_2063_, lean_object* v_i_2064_, lean_object* v_as_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_2060_, v_origAllocId_2061_, v_isSharedId_2062_, v_resultType_2063_, v_i_2064_, v_as_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object* v_resetTokenId_2072_, lean_object* v_code_2073_, lean_object* v_origAllocId_2074_, lean_object* v_isSharedId_2075_, lean_object* v_currentRetType_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2072_, v_code_2073_, v_origAllocId_2074_, v_isSharedId_2075_, v_currentRetType_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object* v_currentRetType_2092_, lean_object* v_ds_2093_, lean_object* v_decl_2094_, lean_object* v_nFields_2095_, lean_object* v_origAllocId_2096_, lean_object* v_k_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_2095_, v_origAllocId_2096_, v_ds_2093_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v_fst_2105_; lean_object* v_snd_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2227_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
v_fst_2105_ = lean_ctor_get(v_a_2104_, 0);
v_snd_2106_ = lean_ctor_get(v_a_2104_, 1);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_a_2104_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2108_ = v_a_2104_;
v_isShared_2109_ = v_isSharedCheck_2227_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_snd_2106_);
lean_inc(v_fst_2105_);
lean_dec(v_a_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2227_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1));
v___x_2111_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2110_, v_a_2099_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; uint8_t v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = 1;
v___x_2114_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_2115_ = 0;
v___x_2116_ = l_Lean_Compiler_LCNF_mkParam(v___x_2113_, v_a_2112_, v___x_2114_, v___x_2115_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_fvarId_2118_; lean_object* v_binderName_2119_; lean_object* v_fvarId_2120_; lean_object* v___x_2121_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v_fvarId_2118_ = lean_ctor_get(v_decl_2094_, 0);
v_binderName_2119_ = lean_ctor_get(v_decl_2094_, 1);
v_fvarId_2120_ = lean_ctor_get(v_a_2117_, 0);
lean_inc_ref(v_currentRetType_2092_);
lean_inc(v_fvarId_2120_);
lean_inc(v_origAllocId_2096_);
lean_inc(v_fvarId_2118_);
v___x_2121_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_fvarId_2118_, v_k_2097_, v_origAllocId_2096_, v_fvarId_2120_, v_currentRetType_2092_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_currentRetType_2092_);
v___x_2124_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_a_2122_, v___x_2123_, v_currentRetType_2092_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2210_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2210_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2210_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3));
v___x_2130_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2129_, v_a_2099_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_binderName_2119_);
lean_inc(v_fvarId_2118_);
v___x_2133_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2133_, 0, v_fvarId_2118_);
lean_ctor_set(v___x_2133_, 1, v_binderName_2119_);
lean_ctor_set(v___x_2133_, 2, v___x_2132_);
lean_ctor_set_uint8(v___x_2133_, sizeof(void*)*3, v___x_2115_);
v___x_2134_ = lean_unsigned_to_nat(2u);
v___x_2135_ = lean_mk_empty_array_with_capacity(v___x_2134_);
v___x_2136_ = lean_array_push(v___x_2135_, v___x_2133_);
v___x_2137_ = lean_array_push(v___x_2136_, v_a_2117_);
lean_inc_ref(v_currentRetType_2092_);
v___x_2138_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_2113_, v_a_2131_, v_currentRetType_2092_, v___x_2137_, v_a_2125_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5));
v___x_2141_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2140_, v_a_2099_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
lean_inc(v_origAllocId_2096_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set_tag(v___x_2127_, 15);
lean_ctor_set(v___x_2127_, 0, v_origAllocId_2096_);
v___x_2144_ = v___x_2127_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_origAllocId_2096_);
v___x_2144_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2113_, v_a_2142_, v___x_2114_, v___x_2144_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v_fvarId_2147_; lean_object* v_fvarId_2148_; lean_object* v___x_2149_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v_fvarId_2147_ = lean_ctor_get(v_a_2139_, 0);
v_fvarId_2148_ = lean_ctor_get(v_a_2146_, 0);
lean_inc(v_fvarId_2148_);
lean_inc(v_fvarId_2147_);
lean_inc(v_origAllocId_2096_);
v___x_2149_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_2096_, v_snd_2106_, v_fvarId_2147_, v_fvarId_2148_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
lean_inc(v_fvarId_2148_);
lean_inc(v_fvarId_2147_);
v___x_2151_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_2096_, v_snd_2106_, v_fvarId_2147_, v_fvarId_2148_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
lean_dec(v_snd_2106_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
lean_inc(v_fvarId_2148_);
v___x_2153_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_fvarId_2148_, v___x_2114_, v_currentRetType_2092_, v_a_2150_, v_a_2152_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2113_, v_decl_2094_, v_a_2099_);
lean_dec_ref(v_decl_2094_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2167_; 
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; 
v_unused_2168_ = lean_ctor_get(v___x_2155_, 0);
lean_dec(v_unused_2168_);
v___x_2157_ = v___x_2155_;
v_isShared_2158_ = v_isSharedCheck_2167_;
goto v_resetjp_2156_;
}
else
{
lean_dec(v___x_2155_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2167_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v_a_2154_);
lean_ctor_set(v___x_2108_, 0, v_a_2146_);
v___x_2160_ = v___x_2108_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2146_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_a_2154_);
v___x_2160_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2161_, 0, v_a_2139_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2113_, v_fst_2105_, v___x_2161_);
lean_dec(v_fst_2105_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2162_);
v___x_2164_ = v___x_2157_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_a_2154_);
lean_dec(v_a_2146_);
lean_dec(v_a_2139_);
lean_del_object(v___x_2108_);
lean_dec(v_fst_2105_);
v_a_2169_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2155_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2155_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_dec(v_a_2146_);
lean_dec(v_a_2139_);
lean_del_object(v___x_2108_);
lean_dec(v_fst_2105_);
lean_dec_ref(v_decl_2094_);
return v___x_2153_;
}
}
else
{
lean_dec(v_a_2150_);
lean_dec(v_a_2146_);
lean_dec(v_a_2139_);
lean_del_object(v___x_2108_);
lean_dec(v_fst_2105_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
return v___x_2151_;
}
}
else
{
lean_dec(v_a_2146_);
lean_dec(v_a_2139_);
lean_del_object(v___x_2108_);
lean_dec(v_snd_2106_);
lean_dec(v_fst_2105_);
lean_dec(v_origAllocId_2096_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
return v___x_2149_;
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_a_2139_);
lean_del_object(v___x_2108_);
lean_dec(v_snd_2106_);
lean_dec(v_fst_2105_);
lean_dec(v_origAllocId_2096_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
v_a_2177_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2145_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2145_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_a_2139_);
lean_del_object(v___x_2127_);
lean_del_object(v___x_2108_);
lean_dec(v_snd_2106_);
lean_dec(v_fst_2105_);
lean_dec(v_origAllocId_2096_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
v_a_2186_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2141_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2141_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_del_object(v___x_2127_);
lean_del_object(v___x_2108_);
lean_dec(v_snd_2106_);
lean_dec(v_fst_2105_);
lean_dec(v_origAllocId_2096_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
v_a_2194_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2138_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2138_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_del_object(v___x_2127_);
lean_dec(v_a_2125_);
lean_dec(v_a_2117_);
lean_del_object(v___x_2108_);
lean_dec(v_snd_2106_);
lean_dec(v_fst_2105_);
lean_dec(v_origAllocId_2096_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
v_a_2202_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2130_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2130_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_dec(v_a_2117_);
lean_del_object(v___x_2108_);
lean_dec(v_snd_2106_);
lean_dec(v_fst_2105_);
lean_dec(v_origAllocId_2096_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
return v___x_2124_;
}
}
else
{
lean_dec(v_a_2117_);
lean_del_object(v___x_2108_);
lean_dec(v_snd_2106_);
lean_dec(v_fst_2105_);
lean_dec(v_origAllocId_2096_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
return v___x_2121_;
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_del_object(v___x_2108_);
lean_dec(v_snd_2106_);
lean_dec(v_fst_2105_);
lean_dec_ref(v_k_2097_);
lean_dec(v_origAllocId_2096_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
v_a_2211_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2116_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2116_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_del_object(v___x_2108_);
lean_dec(v_snd_2106_);
lean_dec(v_fst_2105_);
lean_dec_ref(v_k_2097_);
lean_dec(v_origAllocId_2096_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
v_a_2219_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2111_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2111_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v_k_2097_);
lean_dec(v_origAllocId_2096_);
lean_dec_ref(v_decl_2094_);
lean_dec_ref(v_currentRetType_2092_);
v_a_2228_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2103_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2103_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object* v_resultType_2236_, lean_object* v_x_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(v_resultType_2236_, v_x_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object* v_resultType_2244_, lean_object* v_i_2245_, lean_object* v_as_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = lean_array_get_size(v_as_2246_);
v___x_2253_ = lean_nat_dec_lt(v_i_2245_, v___x_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
lean_dec(v_i_2245_);
lean_dec_ref(v_resultType_2244_);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_as_2246_);
return v___x_2254_;
}
else
{
lean_object* v___f_2255_; lean_object* v_a_2256_; lean_object* v___x_2257_; 
lean_inc_ref(v_resultType_2244_);
v___f_2255_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2255_, 0, v_resultType_2244_);
v_a_2256_ = lean_array_fget_borrowed(v_as_2246_, v_i_2245_);
lean_inc(v_a_2256_);
v___x_2257_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_2256_, v___f_2255_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; size_t v___x_2259_; size_t v___x_2260_; uint8_t v___x_2261_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v___x_2259_ = lean_ptr_addr(v_a_2256_);
v___x_2260_ = lean_ptr_addr(v_a_2258_);
v___x_2261_ = lean_usize_dec_eq(v___x_2259_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = lean_nat_add(v_i_2245_, v___x_2262_);
v___x_2264_ = lean_array_fset(v_as_2246_, v_i_2245_, v_a_2258_);
lean_dec(v_i_2245_);
v_i_2245_ = v___x_2263_;
v_as_2246_ = v___x_2264_;
goto _start;
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec(v_a_2258_);
v___x_2266_ = lean_unsigned_to_nat(1u);
v___x_2267_ = lean_nat_add(v_i_2245_, v___x_2266_);
lean_dec(v_i_2245_);
v_i_2245_ = v___x_2267_;
goto _start;
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref(v_as_2246_);
lean_dec(v_i_2245_);
lean_dec_ref(v_resultType_2244_);
v_a_2269_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2257_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2257_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object* v_code_2277_, lean_object* v_ds_2278_, lean_object* v_currentRetType_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_code_2286_; lean_object* v_ds_2287_; lean_object* v_k_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; 
switch(lean_obj_tag(v_code_2277_))
{
case 0:
{
lean_object* v_decl_2297_; lean_object* v_value_2298_; 
v_decl_2297_ = lean_ctor_get(v_code_2277_, 0);
v_value_2298_ = lean_ctor_get(v_decl_2297_, 3);
if (lean_obj_tag(v_value_2298_) == 11)
{
lean_object* v_k_2299_; lean_object* v_n_2300_; lean_object* v_var_2301_; lean_object* v___x_2302_; 
lean_inc_ref(v_decl_2297_);
v_k_2299_ = lean_ctor_get(v_code_2277_, 1);
lean_inc_ref(v_k_2299_);
lean_dec_ref_known(v_code_2277_, 2);
v_n_2300_ = lean_ctor_get(v_value_2298_, 0);
lean_inc(v_n_2300_);
v_var_2301_ = lean_ctor_get(v_value_2298_, 1);
lean_inc(v_var_2301_);
v___x_2302_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2279_, v_ds_2278_, v_decl_2297_, v_n_2300_, v_var_2301_, v_k_2299_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_2302_;
}
else
{
lean_object* v_k_2303_; 
v_k_2303_ = lean_ctor_get(v_code_2277_, 1);
lean_inc_ref(v_k_2303_);
v_code_2286_ = v_code_2277_;
v_ds_2287_ = v_ds_2278_;
v_k_2288_ = v_k_2303_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
goto v___jp_2285_;
}
}
case 2:
{
lean_object* v_decl_2304_; lean_object* v_k_2305_; lean_object* v_params_2306_; lean_object* v_type_2307_; lean_object* v_value_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_decl_2304_ = lean_ctor_get(v_code_2277_, 0);
lean_inc_ref(v_decl_2304_);
v_k_2305_ = lean_ctor_get(v_code_2277_, 1);
lean_inc_ref(v_k_2305_);
lean_dec_ref_known(v_code_2277_, 2);
v_params_2306_ = lean_ctor_get(v_decl_2304_, 2);
lean_inc_ref(v_params_2306_);
v_type_2307_ = lean_ctor_get(v_decl_2304_, 3);
lean_inc_ref_n(v_type_2307_, 2);
v_value_2308_ = lean_ctor_get(v_decl_2304_, 4);
v___x_2309_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_value_2308_);
v___x_2310_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_value_2308_, v___x_2309_, v_type_2307_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2331_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2331_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2331_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
uint8_t v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = 1;
v___x_2316_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2315_, v_decl_2304_, v_type_2307_, v_params_2306_, v_a_2311_, v_a_2281_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
if (v_isShared_2314_ == 0)
{
lean_ctor_set_tag(v___x_2313_, 2);
lean_ctor_set(v___x_2313_, 0, v_a_2317_);
v___x_2319_ = v___x_2313_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2317_);
v___x_2319_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_array_push(v_ds_2278_, v___x_2319_);
v_code_2277_ = v_k_2305_;
v_ds_2278_ = v___x_2320_;
goto _start;
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_del_object(v___x_2313_);
lean_dec_ref(v_k_2305_);
lean_dec_ref(v_currentRetType_2279_);
lean_dec_ref(v_ds_2278_);
v_a_2323_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2316_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2316_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_2307_);
lean_dec_ref(v_params_2306_);
lean_dec_ref(v_k_2305_);
lean_dec_ref(v_decl_2304_);
lean_dec_ref(v_currentRetType_2279_);
lean_dec_ref(v_ds_2278_);
return v___x_2310_;
}
}
case 4:
{
lean_object* v_cases_2332_; lean_object* v_typeName_2333_; lean_object* v_resultType_2334_; lean_object* v_discr_2335_; lean_object* v_alts_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v_currentRetType_2279_);
v_cases_2332_ = lean_ctor_get(v_code_2277_, 0);
lean_inc_ref(v_cases_2332_);
v_typeName_2333_ = lean_ctor_get(v_cases_2332_, 0);
v_resultType_2334_ = lean_ctor_get(v_cases_2332_, 1);
v_discr_2335_ = lean_ctor_get(v_cases_2332_, 2);
v_alts_2336_ = lean_ctor_get(v_cases_2332_, 3);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_cases_2332_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2338_ = v_cases_2332_;
v_isShared_2339_ = v_isSharedCheck_2376_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_alts_2336_);
lean_inc(v_discr_2335_);
lean_inc(v_resultType_2334_);
lean_inc(v_typeName_2333_);
lean_dec(v_cases_2332_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2376_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2336_);
lean_inc_ref(v_resultType_2334_);
v___x_2341_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2334_, v___x_2340_, v_alts_2336_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2367_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2367_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2367_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
uint8_t v___x_2346_; lean_object* v___y_2348_; size_t v___x_2353_; size_t v___x_2354_; uint8_t v___x_2355_; 
v___x_2346_ = 1;
v___x_2353_ = lean_ptr_addr(v_alts_2336_);
lean_dec_ref(v_alts_2336_);
v___x_2354_ = lean_ptr_addr(v_a_2342_);
v___x_2355_ = lean_usize_dec_eq(v___x_2353_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2365_; 
v_isSharedCheck_2365_ = !lean_is_exclusive(v_code_2277_);
if (v_isSharedCheck_2365_ == 0)
{
lean_object* v_unused_2366_; 
v_unused_2366_ = lean_ctor_get(v_code_2277_, 0);
lean_dec(v_unused_2366_);
v___x_2357_ = v_code_2277_;
v_isShared_2358_ = v_isSharedCheck_2365_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v_code_2277_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2365_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 3, v_a_2342_);
v___x_2360_ = v___x_2338_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_typeName_2333_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_resultType_2334_);
lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_discr_2335_);
lean_ctor_set(v_reuseFailAlloc_2364_, 3, v_a_2342_);
v___x_2360_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2360_);
v___x_2362_ = v___x_2357_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
v___y_2348_ = v___x_2362_;
goto v___jp_2347_;
}
}
}
}
else
{
lean_dec(v_a_2342_);
lean_del_object(v___x_2338_);
lean_dec(v_discr_2335_);
lean_dec_ref(v_resultType_2334_);
lean_dec(v_typeName_2333_);
v___y_2348_ = v_code_2277_;
goto v___jp_2347_;
}
v___jp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2349_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2346_, v_ds_2278_, v___y_2348_);
lean_dec_ref(v_ds_2278_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2349_);
v___x_2351_ = v___x_2344_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_del_object(v___x_2338_);
lean_dec_ref(v_alts_2336_);
lean_dec(v_discr_2335_);
lean_dec_ref(v_resultType_2334_);
lean_dec(v_typeName_2333_);
lean_dec_ref_known(v_code_2277_, 1);
lean_dec_ref(v_ds_2278_);
v_a_2368_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2341_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2341_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
case 7:
{
lean_object* v_k_2377_; 
v_k_2377_ = lean_ctor_get(v_code_2277_, 3);
lean_inc_ref(v_k_2377_);
v_code_2286_ = v_code_2277_;
v_ds_2287_ = v_ds_2278_;
v_k_2288_ = v_k_2377_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
goto v___jp_2285_;
}
case 8:
{
lean_object* v_k_2378_; 
v_k_2378_ = lean_ctor_get(v_code_2277_, 3);
lean_inc_ref(v_k_2378_);
v_code_2286_ = v_code_2277_;
v_ds_2287_ = v_ds_2278_;
v_k_2288_ = v_k_2378_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
goto v___jp_2285_;
}
case 9:
{
lean_object* v_k_2379_; 
v_k_2379_ = lean_ctor_get(v_code_2277_, 5);
lean_inc_ref(v_k_2379_);
v_code_2286_ = v_code_2277_;
v_ds_2287_ = v_ds_2278_;
v_k_2288_ = v_k_2379_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
goto v___jp_2285_;
}
case 10:
{
lean_object* v_k_2380_; 
v_k_2380_ = lean_ctor_get(v_code_2277_, 2);
lean_inc_ref(v_k_2380_);
v_code_2286_ = v_code_2277_;
v_ds_2287_ = v_ds_2278_;
v_k_2288_ = v_k_2380_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
goto v___jp_2285_;
}
case 11:
{
lean_object* v_k_2381_; 
v_k_2381_ = lean_ctor_get(v_code_2277_, 2);
lean_inc_ref(v_k_2381_);
v_code_2286_ = v_code_2277_;
v_ds_2287_ = v_ds_2278_;
v_k_2288_ = v_k_2381_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
goto v___jp_2285_;
}
case 12:
{
lean_object* v_k_2382_; 
v_k_2382_ = lean_ctor_get(v_code_2277_, 3);
lean_inc_ref(v_k_2382_);
v_code_2286_ = v_code_2277_;
v_ds_2287_ = v_ds_2278_;
v_k_2288_ = v_k_2382_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
goto v___jp_2285_;
}
case 13:
{
lean_object* v_k_2383_; 
v_k_2383_ = lean_ctor_get(v_code_2277_, 1);
lean_inc_ref(v_k_2383_);
v_code_2286_ = v_code_2277_;
v_ds_2287_ = v_ds_2278_;
v_k_2288_ = v_k_2383_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
goto v___jp_2285_;
}
default: 
{
uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v_currentRetType_2279_);
v___x_2384_ = 1;
v___x_2385_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2384_, v_ds_2278_, v_code_2277_);
lean_dec_ref(v_ds_2278_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
}
v___jp_2285_:
{
uint8_t v___x_2293_; lean_object* v_d_2294_; lean_object* v___x_2295_; 
v___x_2293_ = 1;
v_d_2294_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_2293_, v_code_2286_);
lean_dec_ref(v_code_2286_);
v___x_2295_ = lean_array_push(v_ds_2287_, v_d_2294_);
v_code_2277_ = v_k_2288_;
v_ds_2278_ = v___x_2295_;
v_a_2280_ = v___y_2289_;
v_a_2281_ = v___y_2290_;
v_a_2282_ = v___y_2291_;
v_a_2283_ = v___y_2292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object* v_resultType_2387_, lean_object* v_x_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2395_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2388_, v___x_2394_, v_resultType_2387_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object* v_resultType_2396_, lean_object* v_i_2397_, lean_object* v_as_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2396_, v_i_2397_, v_as_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object* v_code_2405_, lean_object* v_ds_2406_, lean_object* v_currentRetType_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_code_2405_, v_ds_2406_, v_currentRetType_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object* v_currentRetType_2414_, lean_object* v_ds_2415_, lean_object* v_decl_2416_, lean_object* v_nFields_2417_, lean_object* v_origAllocId_2418_, lean_object* v_k_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2414_, v_ds_2415_, v_decl_2416_, v_nFields_2417_, v_origAllocId_2418_, v_k_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object* v_f_2426_, lean_object* v_v_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
if (lean_obj_tag(v_v_2427_) == 0)
{
lean_object* v_code_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2457_; 
v_code_2433_ = lean_ctor_get(v_v_2427_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_v_2427_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2435_ = v_v_2427_;
v_isShared_2436_ = v_isSharedCheck_2457_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_code_2433_);
lean_dec(v_v_2427_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2457_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; 
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2430_);
lean_inc(v___y_2429_);
lean_inc_ref(v___y_2428_);
v___x_2437_ = lean_apply_6(v_f_2426_, v_code_2433_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, lean_box(0));
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2448_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2448_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2448_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v_a_2438_);
v___x_2443_ = v___x_2435_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2445_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2443_);
v___x_2445_ = v___x_2440_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_del_object(v___x_2435_);
v_a_2449_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2437_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2437_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
else
{
lean_object* v___x_2458_; 
lean_dec_ref(v_f_2426_);
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v_v_2427_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object* v_f_2459_, lean_object* v_v_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2459_, v_v_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t v_pu_2467_, lean_object* v_f_2468_, lean_object* v_v_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2468_, v_v_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object* v_pu_2476_, lean_object* v_f_2477_, lean_object* v_v_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
uint8_t v_pu_boxed_2484_; lean_object* v_res_2485_; 
v_pu_boxed_2484_ = lean_unbox(v_pu_2476_);
v_res_2485_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(v_pu_boxed_2484_, v_f_2477_, v_v_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object* v_toSignature_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_type_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v_type_2493_ = lean_ctor_get(v_toSignature_2486_, 2);
lean_inc_ref(v_type_2493_);
lean_dec_ref(v_toSignature_2486_);
v___x_2494_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2495_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2487_, v___x_2494_, v_type_2493_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object* v_toSignature_2496_, lean_object* v_x_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(v_toSignature_2496_, v_x_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object* v_decl_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2505_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2548_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2548_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2548_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
uint8_t v_resetReuse_2515_; 
v_resetReuse_2515_ = lean_ctor_get_uint8(v_a_2511_, sizeof(void*)*4 + 2);
lean_dec(v_a_2511_);
if (v_resetReuse_2515_ == 0)
{
lean_object* v___x_2517_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v_decl_2504_);
v___x_2517_ = v___x_2513_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_decl_2504_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
else
{
lean_object* v_toSignature_2519_; lean_object* v_value_2520_; uint8_t v_recursive_2521_; lean_object* v_inlineAttr_x3f_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2547_; 
lean_del_object(v___x_2513_);
v_toSignature_2519_ = lean_ctor_get(v_decl_2504_, 0);
v_value_2520_ = lean_ctor_get(v_decl_2504_, 1);
v_recursive_2521_ = lean_ctor_get_uint8(v_decl_2504_, sizeof(void*)*3);
v_inlineAttr_x3f_2522_ = lean_ctor_get(v_decl_2504_, 2);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_decl_2504_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2524_ = v_decl_2504_;
v_isShared_2525_ = v_isSharedCheck_2547_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_inlineAttr_x3f_2522_);
lean_inc(v_value_2520_);
lean_inc(v_toSignature_2519_);
lean_dec(v_decl_2504_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2547_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___f_2526_; lean_object* v___x_2527_; 
lean_inc_ref(v_toSignature_2519_);
v___f_2526_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2526_, 0, v_toSignature_2519_);
v___x_2527_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v___f_2526_, v_value_2520_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2538_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2538_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2538_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v_a_2528_);
v___x_2533_ = v___x_2524_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_toSignature_2519_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_a_2528_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_inlineAttr_x3f_2522_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, sizeof(void*)*3, v_recursive_2521_);
v___x_2533_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2535_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v___x_2533_);
v___x_2535_ = v___x_2530_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_del_object(v___x_2524_);
lean_dec(v_inlineAttr_x3f_2522_);
lean_dec_ref(v_toSignature_2519_);
v_a_2539_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2527_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2527_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec_ref(v_decl_2504_);
v_a_2549_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2510_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2510_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object* v_decl_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(v_decl_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
return v_res_2563_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2568_ = lean_unsigned_to_nat(0u);
v___x_2569_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__2));
v___x_2570_ = 2;
v___x_2571_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__1));
v___x_2572_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_2571_, v___x_2570_, v___x_2569_, v___x_2568_);
return v___x_2572_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse(void){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_obj_once(&l_Lean_Compiler_LCNF_expandResetReuse___closed__3, &l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3);
return v___x_2573_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_unsigned_to_nat(2743268278u);
v___x_2630_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2631_ = l_Lean_Name_num___override(v___x_2630_, v___x_2629_);
return v___x_2631_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2634_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2635_ = l_Lean_Name_str___override(v___x_2634_, v___x_2633_);
return v___x_2635_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2638_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2639_ = l_Lean_Name_str___override(v___x_2638_, v___x_2637_);
return v___x_2639_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = lean_unsigned_to_nat(2u);
v___x_2641_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2642_ = l_Lean_Name_num___override(v___x_2641_, v___x_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2644_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2645_ = 1;
v___x_2646_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2647_ = l_Lean_registerTraceClass(v___x_2644_, v___x_2645_, v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
return v_res_2649_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
