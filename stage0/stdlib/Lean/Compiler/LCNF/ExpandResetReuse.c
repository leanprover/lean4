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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.ExpandResetReuse"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.eraseProjIncFor"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__2_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "assertion violation: n > 0 -- 0 incs should not be happening\n      "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_2048__overap_43_; lean_object* v___x_44_; 
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
v___x_2048__overap_43_ = lean_panic_fn_borrowed(v___f_42_, v_msg_5_);
lean_dec_ref(v___f_42_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
v___x_44_ = lean_apply_5(v___x_2048__overap_43_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
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
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0(void){
_start:
{
uint8_t v___x_58_; lean_object* v___x_59_; 
v___x_58_ = 1;
v___x_59_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_63_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__3));
v___x_64_ = lean_unsigned_to_nat(6u);
v___x_65_ = lean_unsigned_to_nat(87u);
v___x_66_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__2));
v___x_67_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1));
v___x_68_ = l_mkPanicMessageWithDecl(v___x_67_, v___x_66_, v___x_65_, v___x_64_, v___x_63_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object* v_targetId_69_, lean_object* v_b_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___y_77_; lean_object* v___y_78_; lean_object* v___y_79_; lean_object* v_snd_83_; lean_object* v_fst_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_218_; 
v_snd_83_ = lean_ctor_get(v_b_70_, 1);
v_fst_84_ = lean_ctor_get(v_b_70_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_b_70_);
if (v_isSharedCheck_218_ == 0)
{
v___x_86_ = v_b_70_;
v_isShared_87_ = v_isSharedCheck_218_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_snd_83_);
lean_inc(v_fst_84_);
lean_dec(v_b_70_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_218_;
goto v_resetjp_85_;
}
v___jp_76_:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v___y_79_);
lean_ctor_set(v___x_80_, 1, v___y_77_);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___y_78_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v_b_70_ = v___x_81_;
goto _start;
}
v_resetjp_85_:
{
lean_object* v_fst_88_; lean_object* v_snd_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_217_; 
v_fst_88_ = lean_ctor_get(v_snd_83_, 0);
v_snd_89_ = lean_ctor_get(v_snd_83_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_snd_83_);
if (v_isSharedCheck_217_ == 0)
{
v___x_91_ = v_snd_83_;
v_isShared_92_ = v_isSharedCheck_217_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_snd_89_);
lean_inc(v_fst_88_);
lean_dec(v_snd_83_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_217_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(2u);
v___x_106_ = lean_array_get_size(v_fst_84_);
v___x_107_ = lean_nat_dec_le(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
lean_del_object(v___x_91_);
lean_del_object(v___x_86_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_fst_88_);
lean_ctor_set(v___x_108_, 1, v_snd_89_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_fst_84_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_d_114_; 
v___x_111_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_sub(v___x_106_, v___x_112_);
v_d_114_ = lean_array_get(v___x_111_, v_fst_84_, v___x_113_);
lean_dec(v___x_113_);
switch(lean_obj_tag(v_d_114_))
{
case 0:
{
lean_object* v_decl_115_; lean_object* v_value_116_; 
v_decl_115_ = lean_ctor_get(v_d_114_, 0);
v_value_116_ = lean_ctor_get(v_decl_115_, 3);
lean_inc(v_value_116_);
switch(lean_obj_tag(v_value_116_))
{
case 8:
{
lean_object* v_ds_117_; lean_object* v_keep_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec_ref(v_value_116_);
lean_del_object(v___x_91_);
lean_del_object(v___x_86_);
v_ds_117_ = lean_array_pop(v_fst_84_);
v_keep_118_ = lean_array_push(v_fst_88_, v_d_114_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_keep_118_);
lean_ctor_set(v___x_119_, 1, v_snd_89_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v_ds_117_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v_b_70_ = v___x_120_;
goto _start;
}
case 7:
{
lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_132_; 
lean_del_object(v___x_91_);
lean_del_object(v___x_86_);
v_isSharedCheck_132_ = !lean_is_exclusive(v_value_116_);
if (v_isSharedCheck_132_ == 0)
{
lean_object* v_unused_133_; lean_object* v_unused_134_; 
v_unused_133_ = lean_ctor_get(v_value_116_, 1);
lean_dec(v_unused_133_);
v_unused_134_ = lean_ctor_get(v_value_116_, 0);
lean_dec(v_unused_134_);
v___x_123_ = v_value_116_;
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
else
{
lean_dec(v_value_116_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_ds_125_; lean_object* v_keep_126_; lean_object* v___x_128_; 
v_ds_125_ = lean_array_pop(v_fst_84_);
v_keep_126_ = lean_array_push(v_fst_88_, v_d_114_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 0);
lean_ctor_set(v___x_123_, 1, v_snd_89_);
lean_ctor_set(v___x_123_, 0, v_keep_126_);
v___x_128_ = v___x_123_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_keep_126_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_snd_89_);
v___x_128_ = v_reuseFailAlloc_131_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_ds_125_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v_b_70_ = v___x_129_;
goto _start;
}
}
}
default: 
{
lean_dec(v_value_116_);
lean_dec_ref(v_d_114_);
goto v___jp_93_;
}
}
}
case 7:
{
lean_object* v_fvarId_135_; lean_object* v_n_136_; uint8_t v_check_137_; uint8_t v_persistent_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
lean_del_object(v___x_91_);
lean_del_object(v___x_86_);
v_fvarId_135_ = lean_ctor_get(v_d_114_, 0);
v_n_136_ = lean_ctor_get(v_d_114_, 1);
v_check_137_ = lean_ctor_get_uint8(v_d_114_, sizeof(void*)*2);
v_persistent_138_ = lean_ctor_get_uint8(v_d_114_, sizeof(void*)*2 + 1);
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_nat_dec_lt(v___x_139_, v_n_136_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec_ref(v_d_114_);
lean_dec(v_snd_89_);
lean_dec(v_fst_88_);
lean_dec(v_fst_84_);
v___x_141_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4);
v___x_142_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v___x_141_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_153_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_153_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
if (lean_obj_tag(v_a_143_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; 
v_a_147_ = lean_ctor_get(v_a_143_, 0);
lean_inc(v_a_147_);
lean_dec_ref(v_a_143_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v_a_147_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
lean_object* v_a_151_; 
lean_del_object(v___x_145_);
v_a_151_ = lean_ctor_get(v_a_143_, 0);
lean_inc(v_a_151_);
lean_dec_ref(v_a_143_);
v_b_70_ = v_a_151_;
goto _start;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_142_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_142_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v___x_162_; lean_object* v_d_x27_163_; 
v___x_162_ = lean_nat_sub(v___x_106_, v___x_105_);
v_d_x27_163_ = lean_array_get(v___x_111_, v_fst_84_, v___x_162_);
lean_dec(v___x_162_);
if (lean_obj_tag(v_d_x27_163_) == 0)
{
lean_object* v_decl_164_; lean_object* v_value_165_; 
v_decl_164_ = lean_ctor_get(v_d_x27_163_, 0);
v_value_165_ = lean_ctor_get(v_decl_164_, 3);
lean_inc(v_value_165_);
if (lean_obj_tag(v_value_165_) == 6)
{
lean_object* v_fvarId_166_; lean_object* v_i_167_; lean_object* v_var_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_216_; 
v_fvarId_166_ = lean_ctor_get(v_decl_164_, 0);
v_i_167_ = lean_ctor_get(v_value_165_, 0);
v_var_168_ = lean_ctor_get(v_value_165_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_value_165_);
if (v_isSharedCheck_216_ == 0)
{
v___x_170_ = v_value_165_;
v_isShared_171_ = v_isSharedCheck_216_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_var_168_);
lean_inc(v_i_167_);
lean_dec(v_value_165_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_216_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
uint8_t v___y_173_; uint8_t v___x_214_; 
v___x_214_ = l_Lean_instBEqFVarId_beq(v_fvarId_166_, v_fvarId_135_);
if (v___x_214_ == 0)
{
lean_dec(v_var_168_);
v___y_173_ = v___x_214_;
goto v___jp_172_;
}
else
{
uint8_t v___x_215_; 
v___x_215_ = l_Lean_instBEqFVarId_beq(v_targetId_69_, v_var_168_);
lean_dec(v_var_168_);
v___y_173_ = v___x_215_;
goto v___jp_172_;
}
v___jp_172_:
{
if (v___y_173_ == 0)
{
lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_i_167_);
lean_dec_ref(v_d_114_);
v_isSharedCheck_184_ = !lean_is_exclusive(v_d_x27_163_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v_d_x27_163_, 0);
lean_dec(v_unused_185_);
v___x_175_ = v_d_x27_163_;
v_isShared_176_ = v_isSharedCheck_184_;
goto v_resetjp_174_;
}
else
{
lean_dec(v_d_x27_163_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_184_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 0);
lean_ctor_set(v___x_170_, 1, v_snd_89_);
lean_ctor_set(v___x_170_, 0, v_fst_88_);
v___x_178_ = v___x_170_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_fst_88_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_snd_89_);
v___x_178_ = v_reuseFailAlloc_183_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_fst_84_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_179_);
v___x_181_ = v___x_175_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_box(0);
v___x_187_ = lean_array_get_borrowed(v___x_186_, v_snd_89_, v_i_167_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_202_; 
lean_inc(v_n_136_);
lean_inc(v_fvarId_135_);
lean_del_object(v___x_170_);
v_isSharedCheck_202_ = !lean_is_exclusive(v_d_114_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_203_ = lean_ctor_get(v_d_114_, 1);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_d_114_, 0);
lean_dec(v_unused_204_);
v___x_189_ = v_d_114_;
v_isShared_190_ = v_isSharedCheck_202_;
goto v_resetjp_188_;
}
else
{
lean_dec(v_d_114_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_202_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v_ds_192_; lean_object* v___x_193_; lean_object* v_mask_194_; lean_object* v_keep_195_; uint8_t v___x_196_; 
v___x_191_ = lean_array_pop(v_fst_84_);
v_ds_192_ = lean_array_pop(v___x_191_);
lean_inc(v_fvarId_135_);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v_fvarId_135_);
v_mask_194_ = lean_array_set(v_snd_89_, v_i_167_, v___x_193_);
lean_dec(v_i_167_);
v_keep_195_ = lean_array_push(v_fst_88_, v_d_x27_163_);
v___x_196_ = lean_nat_dec_eq(v_n_136_, v___x_112_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_nat_sub(v_n_136_, v___x_112_);
lean_dec(v_n_136_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v___x_197_);
v___x_199_ = v___x_189_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_fvarId_135_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_197_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, sizeof(void*)*2, v_check_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, sizeof(void*)*2 + 1, v_persistent_138_);
v___x_199_ = v_reuseFailAlloc_201_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = lean_array_push(v_keep_195_, v___x_199_);
v___y_77_ = v_mask_194_;
v___y_78_ = v_ds_192_;
v___y_79_ = v___x_200_;
goto v___jp_76_;
}
}
else
{
lean_del_object(v___x_189_);
lean_dec(v_n_136_);
lean_dec(v_fvarId_135_);
v___y_77_ = v_mask_194_;
v___y_78_ = v_ds_192_;
v___y_79_ = v_keep_195_;
goto v___jp_76_;
}
}
}
else
{
lean_object* v_keep_205_; lean_object* v_keep_206_; lean_object* v___x_207_; lean_object* v_ds_208_; lean_object* v___x_210_; 
lean_dec(v_i_167_);
v_keep_205_ = lean_array_push(v_fst_88_, v_d_114_);
v_keep_206_ = lean_array_push(v_keep_205_, v_d_x27_163_);
v___x_207_ = lean_array_pop(v_fst_84_);
v_ds_208_ = lean_array_pop(v___x_207_);
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 0);
lean_ctor_set(v___x_170_, 1, v_snd_89_);
lean_ctor_set(v___x_170_, 0, v_keep_206_);
v___x_210_ = v___x_170_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_keep_206_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_snd_89_);
v___x_210_ = v_reuseFailAlloc_213_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; 
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v_ds_208_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v_b_70_ = v___x_211_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec(v_value_165_);
lean_dec_ref(v_d_x27_163_);
lean_dec_ref(v_d_114_);
goto v___jp_101_;
}
}
else
{
lean_dec(v_d_x27_163_);
lean_dec_ref(v_d_114_);
goto v___jp_101_;
}
}
}
default: 
{
lean_dec(v_d_114_);
goto v___jp_93_;
}
}
}
v___jp_93_:
{
lean_object* v___x_95_; 
if (v_isShared_92_ == 0)
{
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_fst_88_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_snd_89_);
v___x_95_ = v_reuseFailAlloc_100_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_97_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v___x_95_);
v___x_97_ = v___x_86_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_fst_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_95_);
v___x_97_ = v_reuseFailAlloc_99_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
v___jp_101_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v_fst_88_);
lean_ctor_set(v___x_102_, 1, v_snd_89_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_fst_84_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object* v_targetId_219_, lean_object* v_b_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(v_targetId_219_, v_b_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v_targetId_219_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object* v_nFields_229_, lean_object* v_targetId_230_, lean_object* v_ds_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_keep_237_; lean_object* v___x_238_; lean_object* v_mask_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_keep_237_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_238_ = lean_box(0);
v_mask_239_ = lean_mk_array(v_nFields_229_, v___x_238_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v_keep_237_);
lean_ctor_set(v___x_240_, 1, v_mask_239_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_ds_231_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(v_targetId_230_, v___x_241_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_263_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_263_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_263_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_263_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_snd_247_; lean_object* v_fst_248_; lean_object* v_fst_249_; lean_object* v_snd_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_262_; 
v_snd_247_ = lean_ctor_get(v_a_243_, 1);
lean_inc(v_snd_247_);
v_fst_248_ = lean_ctor_get(v_a_243_, 0);
lean_inc(v_fst_248_);
lean_dec(v_a_243_);
v_fst_249_ = lean_ctor_get(v_snd_247_, 0);
v_snd_250_ = lean_ctor_get(v_snd_247_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_snd_247_);
if (v_isSharedCheck_262_ == 0)
{
v___x_252_ = v_snd_247_;
v_isShared_253_ = v_isSharedCheck_262_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_snd_250_);
lean_inc(v_fst_249_);
lean_dec(v_snd_247_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_262_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_254_ = l_Array_reverse___redArg(v_fst_249_);
v___x_255_ = l_Array_append___redArg(v_fst_248_, v___x_254_);
lean_dec_ref(v___x_254_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_255_);
v___x_257_ = v___x_252_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_snd_250_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_257_);
v___x_259_ = v___x_245_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
v_a_264_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_242_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_242_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object* v_nFields_272_, lean_object* v_targetId_273_, lean_object* v_ds_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_272_, v_targetId_273_, v_ds_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_targetId_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object* v_discr_297_, lean_object* v_discrType_298_, lean_object* v_resultType_299_, lean_object* v_t_300_, lean_object* v_e_301_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_303_ = l_Lean_Expr_getAppFn(v_discrType_298_);
v___x_304_ = l_Lean_Expr_constName_x21(v___x_303_);
lean_dec_ref(v___x_303_);
v___x_305_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3));
v___x_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_e_301_);
v___x_307_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6));
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_t_300_);
v___x_309_ = lean_unsigned_to_nat(2u);
v___x_310_ = lean_mk_empty_array_with_capacity(v___x_309_);
v___x_311_ = lean_array_push(v___x_310_, v___x_306_);
v___x_312_ = lean_array_push(v___x_311_, v___x_308_);
v___x_313_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_313_, 0, v___x_304_);
lean_ctor_set(v___x_313_, 1, v_resultType_299_);
lean_ctor_set(v___x_313_, 2, v_discr_297_);
lean_ctor_set(v___x_313_, 3, v___x_312_);
v___x_314_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object* v_discr_316_, lean_object* v_discrType_317_, lean_object* v_resultType_318_, lean_object* v_t_319_, lean_object* v_e_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_316_, v_discrType_317_, v_resultType_318_, v_t_319_, v_e_320_);
lean_dec_ref(v_discrType_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object* v_discr_323_, lean_object* v_discrType_324_, lean_object* v_resultType_325_, lean_object* v_t_326_, lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_323_, v_discrType_324_, v_resultType_325_, v_t_326_, v_e_327_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object* v_discr_334_, lean_object* v_discrType_335_, lean_object* v_resultType_336_, lean_object* v_t_337_, lean_object* v_e_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(v_discr_334_, v_discrType_335_, v_resultType_336_, v_t_337_, v_e_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec_ref(v_discrType_335_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object* v_msg_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0);
v___x_347_ = lean_panic_fn_borrowed(v___x_346_, v_msg_345_);
return v___x_347_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_351_ = lean_unsigned_to_nat(11u);
v___x_352_ = lean_unsigned_to_nat(138u);
v___x_353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0));
v___x_354_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1));
v___x_355_ = l_mkPanicMessageWithDecl(v___x_354_, v___x_353_, v___x_352_, v___x_351_, v___x_350_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object* v_targetId_356_, size_t v_sz_357_, size_t v_i_358_, lean_object* v_bs_359_){
_start:
{
uint8_t v___x_360_; 
v___x_360_ = lean_usize_dec_lt(v_i_358_, v_sz_357_);
if (v___x_360_ == 0)
{
lean_dec(v_targetId_356_);
return v_bs_359_;
}
else
{
lean_object* v_v_361_; lean_object* v___x_362_; lean_object* v_bs_x27_363_; lean_object* v___y_365_; 
v_v_361_ = lean_array_uget(v_bs_359_, v_i_358_);
v___x_362_ = lean_unsigned_to_nat(0u);
v_bs_x27_363_ = lean_array_uset(v_bs_359_, v_i_358_, v___x_362_);
switch(lean_obj_tag(v_v_361_))
{
case 3:
{
lean_object* v_i_370_; lean_object* v_y_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
v_i_370_ = lean_ctor_get(v_v_361_, 1);
v_y_371_ = lean_ctor_get(v_v_361_, 2);
v_isSharedCheck_378_ = !lean_is_exclusive(v_v_361_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v_v_361_, 0);
lean_dec(v_unused_379_);
v___x_373_ = v_v_361_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_y_371_);
lean_inc(v_i_370_);
lean_dec(v_v_361_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
lean_inc(v_targetId_356_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v_targetId_356_);
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_targetId_356_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_i_370_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_y_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v___y_365_ = v___x_376_;
goto v___jp_364_;
}
}
}
case 5:
{
lean_object* v_i_380_; lean_object* v_offset_381_; lean_object* v_y_382_; lean_object* v_ty_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
v_i_380_ = lean_ctor_get(v_v_361_, 1);
v_offset_381_ = lean_ctor_get(v_v_361_, 2);
v_y_382_ = lean_ctor_get(v_v_361_, 3);
v_ty_383_ = lean_ctor_get(v_v_361_, 4);
v_isSharedCheck_390_ = !lean_is_exclusive(v_v_361_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v_v_361_, 0);
lean_dec(v_unused_391_);
v___x_385_ = v_v_361_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_ty_383_);
lean_inc(v_y_382_);
lean_inc(v_offset_381_);
lean_inc(v_i_380_);
lean_dec(v_v_361_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
lean_inc(v_targetId_356_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v_targetId_356_);
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_targetId_356_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_i_380_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_offset_381_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_y_382_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v_ty_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
v___y_365_ = v___x_388_;
goto v___jp_364_;
}
}
}
case 4:
{
lean_object* v_i_392_; lean_object* v_y_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_i_392_ = lean_ctor_get(v_v_361_, 1);
v_y_393_ = lean_ctor_get(v_v_361_, 2);
v_isSharedCheck_400_ = !lean_is_exclusive(v_v_361_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v_v_361_, 0);
lean_dec(v_unused_401_);
v___x_395_ = v_v_361_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_y_393_);
lean_inc(v_i_392_);
lean_dec(v_v_361_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
lean_inc(v_targetId_356_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v_targetId_356_);
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_targetId_356_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_i_392_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_y_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
v___y_365_ = v___x_398_;
goto v___jp_364_;
}
}
}
default: 
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v_v_361_);
v___x_402_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2);
v___x_403_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(v___x_402_);
v___y_365_ = v___x_403_;
goto v___jp_364_;
}
}
v___jp_364_:
{
size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; 
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_358_, v___x_366_);
v___x_368_ = lean_array_uset(v_bs_x27_363_, v_i_358_, v___y_365_);
v_i_358_ = v___x_367_;
v_bs_359_ = v___x_368_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object* v_targetId_404_, lean_object* v_sz_405_, lean_object* v_i_406_, lean_object* v_bs_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_405_);
lean_dec(v_sz_405_);
v_i_boxed_409_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_404_, v_sz_boxed_408_, v_i_boxed_409_, v_bs_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object* v_targetId_411_, lean_object* v_sets_412_){
_start:
{
size_t v_sz_414_; size_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_sz_414_ = lean_array_size(v_sets_412_);
v___x_415_ = ((size_t)0ULL);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_411_, v_sz_414_, v___x_415_, v_sets_412_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object* v_targetId_418_, lean_object* v_sets_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_418_, v_sets_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object* v_targetId_422_, lean_object* v_sets_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_422_, v_sets_423_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object* v_targetId_430_, lean_object* v_sets_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(v_targetId_430_, v_sets_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object* v_fvarId_438_, lean_object* v_i_439_, lean_object* v_y_440_, lean_object* v_a_441_){
_start:
{
if (lean_obj_tag(v_y_440_) == 0)
{
uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = 0;
v___x_444_ = lean_box(v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
else
{
lean_object* v_fvarId_446_; uint8_t v___x_447_; lean_object* v___x_448_; 
v_fvarId_446_ = lean_ctor_get(v_y_440_, 0);
v___x_447_ = 1;
v___x_448_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_447_, v_fvarId_446_, v_a_441_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_476_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_476_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_476_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_476_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
if (lean_obj_tag(v_a_449_) == 1)
{
lean_object* v_val_453_; 
v_val_453_ = lean_ctor_get(v_a_449_, 0);
lean_inc(v_val_453_);
lean_dec_ref(v_a_449_);
if (lean_obj_tag(v_val_453_) == 6)
{
lean_object* v_i_454_; lean_object* v_var_455_; uint8_t v___x_456_; 
v_i_454_ = lean_ctor_get(v_val_453_, 0);
lean_inc(v_i_454_);
v_var_455_ = lean_ctor_get(v_val_453_, 1);
lean_inc(v_var_455_);
lean_dec_ref(v_val_453_);
v___x_456_ = lean_nat_dec_eq(v_i_439_, v_i_454_);
lean_dec(v_i_454_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec(v_var_455_);
v___x_457_ = lean_box(v___x_456_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_457_);
v___x_459_ = v___x_451_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
else
{
uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_461_ = l_Lean_instBEqFVarId_beq(v_fvarId_438_, v_var_455_);
lean_dec(v_var_455_);
v___x_462_ = lean_box(v___x_461_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_462_);
v___x_464_ = v___x_451_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
lean_dec(v_val_453_);
v___x_466_ = 0;
v___x_467_ = lean_box(v___x_466_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_467_);
v___x_469_ = v___x_451_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
else
{
uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec(v_a_449_);
v___x_471_ = 0;
v___x_472_ = lean_box(v___x_471_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_472_);
v___x_474_ = v___x_451_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_448_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_448_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object* v_fvarId_485_, lean_object* v_i_486_, lean_object* v_y_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_485_, v_i_486_, v_y_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec(v_y_487_);
lean_dec(v_i_486_);
lean_dec(v_fvarId_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object* v_fvarId_491_, lean_object* v_i_492_, lean_object* v_y_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_491_, v_i_492_, v_y_493_, v_a_495_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object* v_fvarId_500_, lean_object* v_i_501_, lean_object* v_y_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(v_fvarId_500_, v_i_501_, v_y_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_y_502_);
lean_dec(v_i_501_);
lean_dec(v_fvarId_500_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object* v_fvarId_509_, lean_object* v_i_510_, lean_object* v_y_511_, lean_object* v_a_512_){
_start:
{
uint8_t v___x_514_; lean_object* v___x_515_; 
v___x_514_ = 1;
v___x_515_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_514_, v_y_511_, v_a_512_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_543_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_543_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_543_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_543_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
if (lean_obj_tag(v_a_516_) == 1)
{
lean_object* v_val_520_; 
v_val_520_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_val_520_);
lean_dec_ref(v_a_516_);
if (lean_obj_tag(v_val_520_) == 7)
{
lean_object* v_i_521_; lean_object* v_var_522_; uint8_t v___x_523_; 
v_i_521_ = lean_ctor_get(v_val_520_, 0);
lean_inc(v_i_521_);
v_var_522_ = lean_ctor_get(v_val_520_, 1);
lean_inc(v_var_522_);
lean_dec_ref(v_val_520_);
v___x_523_ = lean_nat_dec_eq(v_i_510_, v_i_521_);
lean_dec(v_i_521_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_var_522_);
v___x_524_ = lean_box(v___x_523_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_524_);
v___x_526_ = v___x_518_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_528_ = l_Lean_instBEqFVarId_beq(v_fvarId_509_, v_var_522_);
lean_dec(v_var_522_);
v___x_529_ = lean_box(v___x_528_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_529_);
v___x_531_ = v___x_518_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
lean_dec(v_val_520_);
v___x_533_ = 0;
v___x_534_ = lean_box(v___x_533_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_534_);
v___x_536_ = v___x_518_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
lean_dec(v_a_516_);
v___x_538_ = 0;
v___x_539_ = lean_box(v___x_538_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_539_);
v___x_541_ = v___x_518_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_544_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_515_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_515_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object* v_fvarId_552_, lean_object* v_i_553_, lean_object* v_y_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_552_, v_i_553_, v_y_554_, v_a_555_);
lean_dec(v_a_555_);
lean_dec(v_y_554_);
lean_dec(v_i_553_);
lean_dec(v_fvarId_552_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object* v_fvarId_558_, lean_object* v_i_559_, lean_object* v_y_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_558_, v_i_559_, v_y_560_, v_a_562_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object* v_fvarId_567_, lean_object* v_i_568_, lean_object* v_y_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(v_fvarId_567_, v_i_568_, v_y_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_y_569_);
lean_dec(v_i_568_);
lean_dec(v_fvarId_567_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object* v_fvarId_576_, lean_object* v_i_577_, lean_object* v_offset_578_, lean_object* v_y_579_, lean_object* v_a_580_){
_start:
{
uint8_t v___x_582_; lean_object* v___x_583_; 
v___x_582_ = 1;
v___x_583_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_582_, v_y_579_, v_a_580_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_615_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_615_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_615_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_615_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
if (lean_obj_tag(v_a_584_) == 1)
{
lean_object* v_val_588_; 
v_val_588_ = lean_ctor_get(v_a_584_, 0);
lean_inc(v_val_588_);
lean_dec_ref(v_a_584_);
if (lean_obj_tag(v_val_588_) == 8)
{
lean_object* v_n_589_; lean_object* v_offset_590_; lean_object* v_var_591_; uint8_t v___y_593_; uint8_t v___x_603_; 
v_n_589_ = lean_ctor_get(v_val_588_, 0);
lean_inc(v_n_589_);
v_offset_590_ = lean_ctor_get(v_val_588_, 1);
lean_inc(v_offset_590_);
v_var_591_ = lean_ctor_get(v_val_588_, 2);
lean_inc(v_var_591_);
lean_dec_ref(v_val_588_);
v___x_603_ = lean_nat_dec_eq(v_i_577_, v_n_589_);
lean_dec(v_n_589_);
if (v___x_603_ == 0)
{
lean_dec(v_offset_590_);
v___y_593_ = v___x_603_;
goto v___jp_592_;
}
else
{
uint8_t v___x_604_; 
v___x_604_ = lean_nat_dec_eq(v_offset_578_, v_offset_590_);
lean_dec(v_offset_590_);
v___y_593_ = v___x_604_;
goto v___jp_592_;
}
v___jp_592_:
{
if (v___y_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_596_; 
lean_dec(v_var_591_);
v___x_594_ = lean_box(v___y_593_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_594_);
v___x_596_ = v___x_586_;
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
v___x_598_ = l_Lean_instBEqFVarId_beq(v_fvarId_576_, v_var_591_);
lean_dec(v_var_591_);
v___x_599_ = lean_box(v___x_598_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_599_);
v___x_601_ = v___x_586_;
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
uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec(v_val_588_);
v___x_605_ = 0;
v___x_606_ = lean_box(v___x_605_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_606_);
v___x_608_ = v___x_586_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
lean_dec(v_a_584_);
v___x_610_ = 0;
v___x_611_ = lean_box(v___x_610_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_611_);
v___x_613_ = v___x_586_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_a_616_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_583_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_583_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object* v_fvarId_624_, lean_object* v_i_625_, lean_object* v_offset_626_, lean_object* v_y_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_624_, v_i_625_, v_offset_626_, v_y_627_, v_a_628_);
lean_dec(v_a_628_);
lean_dec(v_y_627_);
lean_dec(v_offset_626_);
lean_dec(v_i_625_);
lean_dec(v_fvarId_624_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object* v_fvarId_631_, lean_object* v_i_632_, lean_object* v_offset_633_, lean_object* v_y_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_631_, v_i_632_, v_offset_633_, v_y_634_, v_a_636_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object* v_fvarId_641_, lean_object* v_i_642_, lean_object* v_offset_643_, lean_object* v_y_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(v_fvarId_641_, v_i_642_, v_offset_643_, v_y_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_y_644_);
lean_dec(v_offset_643_);
lean_dec(v_i_642_);
lean_dec(v_fvarId_641_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_toApplicative_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_693_; 
v___x_657_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_658_ = l_StateRefT_x27_instMonad___redArg(v___x_657_);
v_toApplicative_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v___x_658_, 1);
lean_dec(v_unused_694_);
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_693_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_toApplicative_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_693_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_toFunctor_663_; lean_object* v_toSeq_664_; lean_object* v_toSeqLeft_665_; lean_object* v_toSeqRight_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_691_; 
v_toFunctor_663_ = lean_ctor_get(v_toApplicative_659_, 0);
v_toSeq_664_ = lean_ctor_get(v_toApplicative_659_, 2);
v_toSeqLeft_665_ = lean_ctor_get(v_toApplicative_659_, 3);
v_toSeqRight_666_ = lean_ctor_get(v_toApplicative_659_, 4);
v_isSharedCheck_691_ = !lean_is_exclusive(v_toApplicative_659_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v_toApplicative_659_, 1);
lean_dec(v_unused_692_);
v___x_668_ = v_toApplicative_659_;
v_isShared_669_ = v_isSharedCheck_691_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_toSeqRight_666_);
lean_inc(v_toSeqLeft_665_);
lean_inc(v_toSeq_664_);
lean_inc(v_toFunctor_663_);
lean_dec(v_toApplicative_659_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_691_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___x_674_; lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___f_677_; lean_object* v___x_679_; 
v___f_670_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_671_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_663_);
v___f_672_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_672_, 0, v_toFunctor_663_);
v___f_673_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_673_, 0, v_toFunctor_663_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___f_672_);
lean_ctor_set(v___x_674_, 1, v___f_673_);
v___f_675_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_675_, 0, v_toSeqRight_666_);
v___f_676_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_676_, 0, v_toSeqLeft_665_);
v___f_677_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_677_, 0, v_toSeq_664_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 4, v___f_675_);
lean_ctor_set(v___x_668_, 3, v___f_676_);
lean_ctor_set(v___x_668_, 2, v___f_677_);
lean_ctor_set(v___x_668_, 1, v___f_670_);
lean_ctor_set(v___x_668_, 0, v___x_674_);
v___x_679_ = v___x_668_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___f_670_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v___f_677_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v___f_676_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v___f_675_);
v___x_679_ = v_reuseFailAlloc_690_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___f_671_);
lean_ctor_set(v___x_661_, 0, v___x_679_);
v___x_681_ = v___x_661_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___f_671_);
v___x_681_ = v_reuseFailAlloc_689_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___f_686_; lean_object* v___x_994__overap_687_; lean_object* v___x_688_; 
v___x_682_ = l_StateRefT_x27_instMonad___redArg(v___x_681_);
v___x_683_ = 0;
v___x_684_ = lean_box(v___x_683_);
v___x_685_ = l_instInhabitedOfMonad___redArg(v___x_682_, v___x_684_);
v___f_686_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_686_, 0, v___x_685_);
v___x_994__overap_687_ = lean_panic_fn_borrowed(v___f_686_, v_msg_651_);
lean_dec_ref(v___f_686_);
lean_inc(v___y_655_);
lean_inc_ref(v___y_654_);
lean_inc(v___y_653_);
lean_inc_ref(v___y_652_);
v___x_688_ = lean_apply_5(v___x_994__overap_687_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, lean_box(0));
return v___x_688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object* v_msg_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v_msg_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
return v_res_701_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_704_ = lean_unsigned_to_nat(13u);
v___x_705_ = lean_unsigned_to_nat(174u);
v___x_706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0));
v___x_707_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1));
v___x_708_ = l_mkPanicMessageWithDecl(v___x_707_, v___x_706_, v___x_705_, v___x_704_, v___x_703_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object* v_selfId_709_, lean_object* v_as_710_, size_t v_sz_711_, size_t v_i_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_a_720_; uint8_t v___x_724_; 
v___x_724_ = lean_usize_dec_lt(v_i_712_, v_sz_711_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_b_713_);
return v___x_725_;
}
else
{
lean_object* v_fst_726_; lean_object* v_snd_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_764_; 
v_fst_726_ = lean_ctor_get(v_b_713_, 0);
v_snd_727_ = lean_ctor_get(v_b_713_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_b_713_);
if (v_isSharedCheck_764_ == 0)
{
v___x_729_ = v_b_713_;
v_isShared_730_ = v_isSharedCheck_764_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snd_727_);
lean_inc(v_fst_726_);
lean_dec(v_b_713_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_764_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v_a_731_; lean_object* v___y_733_; 
v_a_731_ = lean_array_uget_borrowed(v_as_710_, v_i_712_);
switch(lean_obj_tag(v_a_731_))
{
case 3:
{
lean_object* v_i_752_; lean_object* v_y_753_; lean_object* v___x_754_; 
v_i_752_ = lean_ctor_get(v_a_731_, 1);
v_y_753_ = lean_ctor_get(v_a_731_, 2);
v___x_754_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_selfId_709_, v_i_752_, v_y_753_, v___y_715_);
v___y_733_ = v___x_754_;
goto v___jp_732_;
}
case 4:
{
lean_object* v_i_755_; lean_object* v_y_756_; lean_object* v___x_757_; 
v_i_755_ = lean_ctor_get(v_a_731_, 1);
v_y_756_ = lean_ctor_get(v_a_731_, 2);
v___x_757_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_selfId_709_, v_i_755_, v_y_756_, v___y_715_);
v___y_733_ = v___x_757_;
goto v___jp_732_;
}
case 5:
{
lean_object* v_i_758_; lean_object* v_offset_759_; lean_object* v_y_760_; lean_object* v___x_761_; 
v_i_758_ = lean_ctor_get(v_a_731_, 1);
v_offset_759_ = lean_ctor_get(v_a_731_, 2);
v_y_760_ = lean_ctor_get(v_a_731_, 3);
v___x_761_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_selfId_709_, v_i_758_, v_offset_759_, v_y_760_, v___y_715_);
v___y_733_ = v___x_761_;
goto v___jp_732_;
}
default: 
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1);
v___x_763_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v___x_762_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
v___y_733_ = v___x_763_;
goto v___jp_732_;
}
}
v___jp_732_:
{
if (lean_obj_tag(v___y_733_) == 0)
{
lean_object* v_a_734_; uint8_t v___x_735_; 
v_a_734_ = lean_ctor_get(v___y_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref(v___y_733_);
v___x_735_ = lean_unbox(v_a_734_);
lean_dec(v_a_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_738_; 
lean_inc(v_a_731_);
v___x_736_ = lean_array_push(v_fst_726_, v_a_731_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_736_);
v___x_738_ = v___x_729_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_snd_727_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
v_a_720_ = v___x_738_;
goto v___jp_719_;
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_inc(v_a_731_);
v___x_740_ = lean_array_push(v_snd_727_, v_a_731_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_740_);
v___x_742_ = v___x_729_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fst_726_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
v_a_720_ = v___x_742_;
goto v___jp_719_;
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_del_object(v___x_729_);
lean_dec(v_snd_727_);
lean_dec(v_fst_726_);
v_a_744_ = lean_ctor_get(v___y_733_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___y_733_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___y_733_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___y_733_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
v___jp_719_:
{
size_t v___x_721_; size_t v___x_722_; 
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_712_, v___x_721_);
v_i_712_ = v___x_722_;
v_b_713_ = v_a_720_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object* v_selfId_765_, lean_object* v_as_766_, lean_object* v_sz_767_, lean_object* v_i_768_, lean_object* v_b_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
size_t v_sz_boxed_775_; size_t v_i_boxed_776_; lean_object* v_res_777_; 
v_sz_boxed_775_ = lean_unbox_usize(v_sz_767_);
lean_dec(v_sz_767_);
v_i_boxed_776_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_765_, v_as_766_, v_sz_boxed_775_, v_i_boxed_776_, v_b_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec_ref(v_as_766_);
lean_dec(v_selfId_765_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object* v_selfId_780_, lean_object* v_sets_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_787_; size_t v_sz_788_; size_t v___x_789_; lean_object* v___x_790_; 
v___x_787_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0));
v_sz_788_ = lean_array_size(v_sets_781_);
v___x_789_ = ((size_t)0ULL);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_780_, v_sets_781_, v_sz_788_, v___x_789_, v___x_787_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_807_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_807_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_807_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_807_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_fst_795_; lean_object* v_snd_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_806_; 
v_fst_795_ = lean_ctor_get(v_a_791_, 0);
v_snd_796_ = lean_ctor_get(v_a_791_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_a_791_);
if (v_isSharedCheck_806_ == 0)
{
v___x_798_ = v_a_791_;
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_snd_796_);
lean_inc(v_fst_795_);
lean_dec(v_a_791_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v_fst_795_);
lean_ctor_set(v___x_798_, 0, v_snd_796_);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_snd_796_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_fst_795_);
v___x_801_ = v_reuseFailAlloc_805_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_801_);
v___x_803_ = v___x_793_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
else
{
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object* v_selfId_808_, lean_object* v_sets_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_selfId_808_, v_sets_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_sets_809_);
lean_dec(v_selfId_808_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object* v_target_816_, lean_object* v_b_817_){
_start:
{
lean_object* v_snd_819_; 
v_snd_819_ = lean_ctor_get(v_b_817_, 1);
lean_inc(v_snd_819_);
switch(lean_obj_tag(v_snd_819_))
{
case 7:
{
lean_object* v_fst_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_838_; 
v_fst_820_ = lean_ctor_get(v_b_817_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v_b_817_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_b_817_, 1);
lean_dec(v_unused_839_);
v___x_822_ = v_b_817_;
v_isShared_823_ = v_isSharedCheck_838_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_fst_820_);
lean_dec(v_b_817_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_838_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_fvarId_824_; lean_object* v_k_825_; uint8_t v___x_826_; 
v_fvarId_824_ = lean_ctor_get(v_snd_819_, 0);
v_k_825_ = lean_ctor_get(v_snd_819_, 3);
v___x_826_ = l_Lean_instBEqFVarId_beq(v_target_816_, v_fvarId_824_);
if (v___x_826_ == 0)
{
lean_object* v___x_828_; 
if (v_isShared_823_ == 0)
{
v___x_828_ = v___x_822_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_fst_820_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_snd_819_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; 
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
else
{
uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v_sets_833_; lean_object* v___x_835_; 
lean_inc_ref(v_k_825_);
v___x_831_ = 1;
v___x_832_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_831_, v_snd_819_);
lean_dec_ref(v_snd_819_);
v_sets_833_ = lean_array_push(v_fst_820_, v___x_832_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_k_825_);
lean_ctor_set(v___x_822_, 0, v_sets_833_);
v___x_835_ = v___x_822_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_sets_833_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_k_825_);
v___x_835_ = v_reuseFailAlloc_837_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
v_b_817_ = v___x_835_;
goto _start;
}
}
}
}
case 9:
{
lean_object* v_fst_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_858_; 
v_fst_840_ = lean_ctor_get(v_b_817_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_b_817_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_b_817_, 1);
lean_dec(v_unused_859_);
v___x_842_ = v_b_817_;
v_isShared_843_ = v_isSharedCheck_858_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_fst_840_);
lean_dec(v_b_817_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_858_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_fvarId_844_; lean_object* v_k_845_; uint8_t v___x_846_; 
v_fvarId_844_ = lean_ctor_get(v_snd_819_, 0);
v_k_845_ = lean_ctor_get(v_snd_819_, 5);
v___x_846_ = l_Lean_instBEqFVarId_beq(v_target_816_, v_fvarId_844_);
if (v___x_846_ == 0)
{
lean_object* v___x_848_; 
if (v_isShared_843_ == 0)
{
v___x_848_ = v___x_842_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_fst_840_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_snd_819_);
v___x_848_ = v_reuseFailAlloc_850_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; 
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
else
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v_sets_853_; lean_object* v___x_855_; 
lean_inc_ref(v_k_845_);
v___x_851_ = 1;
v___x_852_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_851_, v_snd_819_);
lean_dec_ref(v_snd_819_);
v_sets_853_ = lean_array_push(v_fst_840_, v___x_852_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_k_845_);
lean_ctor_set(v___x_842_, 0, v_sets_853_);
v___x_855_ = v___x_842_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_sets_853_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_k_845_);
v___x_855_ = v_reuseFailAlloc_857_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
v_b_817_ = v___x_855_;
goto _start;
}
}
}
}
case 8:
{
lean_object* v_fst_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_878_; 
v_fst_860_ = lean_ctor_get(v_b_817_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_b_817_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; 
v_unused_879_ = lean_ctor_get(v_b_817_, 1);
lean_dec(v_unused_879_);
v___x_862_ = v_b_817_;
v_isShared_863_ = v_isSharedCheck_878_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_fst_860_);
lean_dec(v_b_817_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_878_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_fvarId_864_; lean_object* v_k_865_; uint8_t v___x_866_; 
v_fvarId_864_ = lean_ctor_get(v_snd_819_, 0);
v_k_865_ = lean_ctor_get(v_snd_819_, 3);
v___x_866_ = l_Lean_instBEqFVarId_beq(v_target_816_, v_fvarId_864_);
if (v___x_866_ == 0)
{
lean_object* v___x_868_; 
if (v_isShared_863_ == 0)
{
v___x_868_ = v___x_862_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_fst_860_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_snd_819_);
v___x_868_ = v_reuseFailAlloc_870_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; 
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
else
{
uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v_sets_873_; lean_object* v___x_875_; 
lean_inc_ref(v_k_865_);
v___x_871_ = 1;
v___x_872_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_871_, v_snd_819_);
lean_dec_ref(v_snd_819_);
v_sets_873_ = lean_array_push(v_fst_860_, v___x_872_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v_k_865_);
lean_ctor_set(v___x_862_, 0, v_sets_873_);
v___x_875_ = v___x_862_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_sets_873_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_k_865_);
v___x_875_ = v_reuseFailAlloc_877_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
v_b_817_ = v___x_875_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_fst_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_fst_880_ = lean_ctor_get(v_b_817_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v_b_817_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v_b_817_, 1);
lean_dec(v_unused_889_);
v___x_882_ = v_b_817_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_fst_880_);
lean_dec(v_b_817_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_fst_880_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_snd_819_);
v___x_885_ = v_reuseFailAlloc_887_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; 
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object* v_target_890_, lean_object* v_b_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_890_, v_b_891_);
lean_dec(v_target_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object* v_target_894_, lean_object* v_k_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_sets_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_sets_901_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v_sets_901_);
lean_ctor_set(v___x_902_, 1, v_k_895_);
v___x_903_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_894_, v___x_902_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_920_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_920_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_920_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_920_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_919_; 
v_fst_908_ = lean_ctor_get(v_a_904_, 0);
v_snd_909_ = lean_ctor_get(v_a_904_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_a_904_);
if (v_isSharedCheck_919_ == 0)
{
v___x_911_ = v_a_904_;
v_isShared_912_ = v_isSharedCheck_919_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_snd_909_);
lean_inc(v_fst_908_);
lean_dec(v_a_904_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_919_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_fst_908_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_snd_909_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_914_);
v___x_916_ = v___x_906_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
else
{
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object* v_target_921_, lean_object* v_k_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_target_921_, v_k_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_target_921_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object* v_target_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_929_, v_b_930_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object* v_target_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(v_target_937_, v_b_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v_target_937_);
return v_res_944_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_box(0);
v___x_952_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3));
v___x_953_ = l_Lean_Expr_const___override(v___x_952_, v___x_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object* v_upperBound_954_, lean_object* v_mask_955_, lean_object* v_origAllocId_956_, lean_object* v_a_957_, lean_object* v_b_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_a_965_; uint8_t v___x_969_; 
v___x_969_ = lean_nat_dec_lt(v_a_957_, v_upperBound_954_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
lean_dec(v_a_957_);
lean_dec(v_origAllocId_956_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v_b_958_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; 
v___x_971_ = lean_array_fget_borrowed(v_mask_955_, v_a_957_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1));
v___x_973_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_972_, v___y_960_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v___x_975_ = 1;
v___x_976_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_origAllocId_956_);
lean_inc(v_a_957_);
v___x_977_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_977_, 0, v_a_957_);
lean_ctor_set(v___x_977_, 1, v_origAllocId_956_);
v___x_978_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_975_, v_a_974_, v___x_976_, v___x_977_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v_fvarId_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref(v___x_978_);
v_fvarId_980_ = lean_ctor_get(v_a_979_, 0);
v___x_981_ = 0;
v___x_982_ = lean_unsigned_to_nat(1u);
lean_inc(v_fvarId_980_);
v___x_983_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v___x_983_, 0, v_fvarId_980_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
lean_ctor_set(v___x_983_, 2, v_b_958_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*3, v___x_969_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*3 + 1, v___x_981_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_a_979_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v_a_965_ = v___x_984_;
goto v___jp_964_;
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v_b_958_);
lean_dec(v_a_957_);
lean_dec(v_origAllocId_956_);
v_a_985_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_978_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_978_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v_b_958_);
lean_dec(v_a_957_);
lean_dec(v_origAllocId_956_);
v_a_993_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_973_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_973_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
v_a_965_ = v_b_958_;
goto v___jp_964_;
}
}
v___jp_964_:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_a_957_, v___x_966_);
lean_dec(v_a_957_);
v_a_957_ = v___x_967_;
v_b_958_ = v_a_965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1001_, lean_object* v_mask_1002_, lean_object* v_origAllocId_1003_, lean_object* v_a_1004_, lean_object* v_b_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1001_, v_mask_1002_, v_origAllocId_1003_, v_a_1004_, v_b_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec_ref(v_mask_1002_);
lean_dec(v_upperBound_1001_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object* v_origAllocId_1012_, lean_object* v_mask_1013_, lean_object* v_resetJpId_1014_, lean_object* v_isSharedId_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_code_1029_; lean_object* v___x_1030_; 
lean_inc(v_origAllocId_1012_);
v___x_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_origAllocId_1012_);
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_isSharedId_1015_);
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = lean_array_get_size(v_mask_1013_);
v___x_1025_ = lean_unsigned_to_nat(2u);
v___x_1026_ = lean_mk_empty_array_with_capacity(v___x_1025_);
v___x_1027_ = lean_array_push(v___x_1026_, v___x_1021_);
v___x_1028_ = lean_array_push(v___x_1027_, v___x_1022_);
v_code_1029_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1029_, 0, v_resetJpId_1014_);
lean_ctor_set(v_code_1029_, 1, v___x_1028_);
v___x_1030_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v___x_1024_, v_mask_1013_, v_origAllocId_1012_, v___x_1023_, v_code_1029_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object* v_origAllocId_1031_, lean_object* v_mask_1032_, lean_object* v_resetJpId_1033_, lean_object* v_isSharedId_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_1031_, v_mask_1032_, v_resetJpId_1033_, v_isSharedId_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec_ref(v_mask_1032_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object* v_upperBound_1041_, lean_object* v_mask_1042_, lean_object* v_origAllocId_1043_, lean_object* v_inst_1044_, lean_object* v_R_1045_, lean_object* v_a_1046_, lean_object* v_b_1047_, lean_object* v_c_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1041_, v_mask_1042_, v_origAllocId_1043_, v_a_1046_, v_b_1047_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1055_, lean_object* v_mask_1056_, lean_object* v_origAllocId_1057_, lean_object* v_inst_1058_, lean_object* v_R_1059_, lean_object* v_a_1060_, lean_object* v_b_1061_, lean_object* v_c_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(v_upperBound_1055_, v_mask_1056_, v_origAllocId_1057_, v_inst_1058_, v_R_1059_, v_a_1060_, v_b_1061_, v_c_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec_ref(v_mask_1056_);
lean_dec(v_upperBound_1055_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object* v_as_1069_, size_t v_sz_1070_, size_t v_i_1071_, lean_object* v_b_1072_){
_start:
{
lean_object* v_a_1075_; uint8_t v___x_1079_; 
v___x_1079_ = lean_usize_dec_lt(v_i_1071_, v_sz_1070_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_b_1072_);
return v___x_1080_;
}
else
{
lean_object* v_a_1081_; 
v_a_1081_ = lean_array_uget_borrowed(v_as_1069_, v_i_1071_);
if (lean_obj_tag(v_a_1081_) == 1)
{
lean_object* v_val_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; 
v_val_1082_ = lean_ctor_get(v_a_1081_, 0);
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = 0;
lean_inc(v_val_1082_);
v___x_1085_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1085_, 0, v_val_1082_);
lean_ctor_set(v___x_1085_, 1, v___x_1083_);
lean_ctor_set(v___x_1085_, 2, v_b_1072_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*3, v___x_1079_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*3 + 1, v___x_1084_);
v_a_1075_ = v___x_1085_;
goto v___jp_1074_;
}
else
{
v_a_1075_ = v_b_1072_;
goto v___jp_1074_;
}
}
v___jp_1074_:
{
size_t v___x_1076_; size_t v___x_1077_; 
v___x_1076_ = ((size_t)1ULL);
v___x_1077_ = lean_usize_add(v_i_1071_, v___x_1076_);
v_i_1071_ = v___x_1077_;
v_b_1072_ = v_a_1075_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object* v_as_1086_, lean_object* v_sz_1087_, lean_object* v_i_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_){
_start:
{
size_t v_sz_boxed_1091_; size_t v_i_boxed_1092_; lean_object* v_res_1093_; 
v_sz_boxed_1091_ = lean_unbox_usize(v_sz_1087_);
lean_dec(v_sz_1087_);
v_i_boxed_1092_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_res_1093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1086_, v_sz_boxed_1091_, v_i_boxed_1092_, v_b_1089_);
lean_dec_ref(v_as_1086_);
return v_res_1093_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_unsigned_to_nat(2u);
v___x_1096_ = lean_mk_empty_array_with_capacity(v___x_1095_);
v___x_1097_ = lean_array_push(v___x_1096_, v___x_1094_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object* v_origAllocId_1098_, lean_object* v_mask_1099_, lean_object* v_resetJpId_1100_, lean_object* v_isSharedId_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_code_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; uint8_t v___x_1113_; lean_object* v_code_1114_; size_t v_sz_1115_; size_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_isSharedId_1101_);
v___x_1108_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0);
v___x_1109_ = lean_array_push(v___x_1108_, v___x_1107_);
v_code_1110_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1110_, 0, v_resetJpId_1100_);
lean_ctor_set(v_code_1110_, 1, v___x_1109_);
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = 1;
v___x_1113_ = 0;
v_code_1114_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_code_1114_, 0, v_origAllocId_1098_);
lean_ctor_set(v_code_1114_, 1, v___x_1111_);
lean_ctor_set(v_code_1114_, 2, v_code_1110_);
lean_ctor_set_uint8(v_code_1114_, sizeof(void*)*3, v___x_1112_);
lean_ctor_set_uint8(v_code_1114_, sizeof(void*)*3 + 1, v___x_1113_);
v_sz_1115_ = lean_array_size(v_mask_1099_);
v___x_1116_ = ((size_t)0ULL);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_mask_1099_, v_sz_1115_, v___x_1116_, v_code_1114_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(lean_object* v_origAllocId_1118_, lean_object* v_mask_1119_, lean_object* v_resetJpId_1120_, lean_object* v_isSharedId_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_1118_, v_mask_1119_, v_resetJpId_1120_, v_isSharedId_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec_ref(v_mask_1119_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(lean_object* v_as_1128_, size_t v_sz_1129_, size_t v_i_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1128_, v_sz_1129_, v_i_1130_, v_b_1131_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(lean_object* v_as_1138_, lean_object* v_sz_1139_, lean_object* v_i_1140_, lean_object* v_b_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
size_t v_sz_boxed_1147_; size_t v_i_boxed_1148_; lean_object* v_res_1149_; 
v_sz_boxed_1147_ = lean_unbox_usize(v_sz_1139_);
lean_dec(v_sz_1139_);
v_i_boxed_1148_ = lean_unbox_usize(v_i_1140_);
lean_dec(v_i_1140_);
v_res_1149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(v_as_1138_, v_sz_boxed_1147_, v_i_boxed_1148_, v_b_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec_ref(v_as_1138_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1150_, lean_object* v_args_1151_, lean_object* v_origAllocId_1152_, lean_object* v_resetTokenId_1153_, lean_object* v_a_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_nat_dec_lt(v_a_1154_, v_upperBound_1150_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec(v_a_1154_);
lean_dec(v_resetTokenId_1153_);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_b_1155_);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_array_fget_borrowed(v_args_1151_, v_a_1154_);
v___x_1161_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_origAllocId_1152_, v_a_1154_, v___x_1160_, v___y_1156_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v_a_1164_; uint8_t v___x_1168_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref(v___x_1161_);
v___x_1168_ = lean_unbox(v_a_1162_);
lean_dec(v_a_1162_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
lean_inc(v___x_1160_);
lean_inc(v_a_1154_);
lean_inc(v_resetTokenId_1153_);
v___x_1169_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1169_, 0, v_resetTokenId_1153_);
lean_ctor_set(v___x_1169_, 1, v_a_1154_);
lean_ctor_set(v___x_1169_, 2, v___x_1160_);
lean_ctor_set(v___x_1169_, 3, v_b_1155_);
v_a_1164_ = v___x_1169_;
goto v___jp_1163_;
}
else
{
v_a_1164_ = v_b_1155_;
goto v___jp_1163_;
}
v___jp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(1u);
v___x_1166_ = lean_nat_add(v_a_1154_, v___x_1165_);
lean_dec(v_a_1154_);
v_a_1154_ = v___x_1166_;
v_b_1155_ = v_a_1164_;
goto _start;
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec_ref(v_b_1155_);
lean_dec(v_a_1154_);
lean_dec(v_resetTokenId_1153_);
v_a_1170_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1161_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1161_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1178_, lean_object* v_args_1179_, lean_object* v_origAllocId_1180_, lean_object* v_resetTokenId_1181_, lean_object* v_a_1182_, lean_object* v_b_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1178_, v_args_1179_, v_origAllocId_1180_, v_resetTokenId_1181_, v_a_1182_, v_b_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec(v_origAllocId_1180_);
lean_dec_ref(v_args_1179_);
lean_dec(v_upperBound_1178_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(lean_object* v_resetTokenId_1187_, lean_object* v_info_1188_, uint8_t v_update_1189_, lean_object* v_args_1190_, lean_object* v_contJpId_1191_, lean_object* v_origAllocId_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_code_1204_; lean_object* v___x_1205_; 
lean_inc_n(v_resetTokenId_1187_, 2);
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_resetTokenId_1187_);
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = lean_array_get_size(v_args_1190_);
v___x_1201_ = lean_unsigned_to_nat(1u);
v___x_1202_ = lean_mk_empty_array_with_capacity(v___x_1201_);
v___x_1203_ = lean_array_push(v___x_1202_, v___x_1198_);
v_code_1204_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1204_, 0, v_contJpId_1191_);
lean_ctor_set(v_code_1204_, 1, v___x_1203_);
v___x_1205_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v___x_1200_, v_args_1190_, v_origAllocId_1192_, v_resetTokenId_1187_, v___x_1199_, v_code_1204_, v_a_1194_);
if (lean_obj_tag(v___x_1205_) == 0)
{
if (v_update_1189_ == 0)
{
lean_dec(v_resetTokenId_1187_);
return v___x_1205_;
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1215_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1215_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1215_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_cidx_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v_cidx_1210_ = lean_ctor_get(v_info_1188_, 1);
lean_inc(v_cidx_1210_);
v___x_1211_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1211_, 0, v_resetTokenId_1187_);
lean_ctor_set(v___x_1211_, 1, v_cidx_1210_);
lean_ctor_set(v___x_1211_, 2, v_a_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1211_);
v___x_1213_ = v___x_1208_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_dec(v_resetTokenId_1187_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(lean_object* v_resetTokenId_1216_, lean_object* v_info_1217_, lean_object* v_update_1218_, lean_object* v_args_1219_, lean_object* v_contJpId_1220_, lean_object* v_origAllocId_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
uint8_t v_update_boxed_1227_; lean_object* v_res_1228_; 
v_update_boxed_1227_ = lean_unbox(v_update_1218_);
v_res_1228_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1216_, v_info_1217_, v_update_boxed_1227_, v_args_1219_, v_contJpId_1220_, v_origAllocId_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_origAllocId_1221_);
lean_dec_ref(v_args_1219_);
lean_dec_ref(v_info_1217_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(lean_object* v_upperBound_1229_, lean_object* v_args_1230_, lean_object* v_origAllocId_1231_, lean_object* v_resetTokenId_1232_, lean_object* v_inst_1233_, lean_object* v_R_1234_, lean_object* v_a_1235_, lean_object* v_b_1236_, lean_object* v_c_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1229_, v_args_1230_, v_origAllocId_1231_, v_resetTokenId_1232_, v_a_1235_, v_b_1236_, v___y_1239_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1244_, lean_object* v_args_1245_, lean_object* v_origAllocId_1246_, lean_object* v_resetTokenId_1247_, lean_object* v_inst_1248_, lean_object* v_R_1249_, lean_object* v_a_1250_, lean_object* v_b_1251_, lean_object* v_c_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(v_upperBound_1244_, v_args_1245_, v_origAllocId_1246_, v_resetTokenId_1247_, v_inst_1248_, v_R_1249_, v_a_1250_, v_b_1251_, v_c_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v_origAllocId_1246_);
lean_dec_ref(v_args_1245_);
lean_dec(v_upperBound_1244_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(lean_object* v_decl_1262_, lean_object* v_info_1263_, lean_object* v_args_1264_, lean_object* v_contJpId_1265_, lean_object* v_selfSets_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1));
v___x_1273_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1272_, v_a_1268_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v_type_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref(v___x_1273_);
v_type_1275_ = lean_ctor_get(v_decl_1262_, 2);
lean_inc_ref(v_type_1275_);
lean_dec_ref(v_decl_1262_);
v___x_1276_ = 1;
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v_info_1263_);
lean_ctor_set(v___x_1277_, 1, v_args_1264_);
v___x_1278_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1276_, v_a_1274_, v_type_1275_, v___x_1277_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v_fvarId_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1296_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
v_fvarId_1280_ = lean_ctor_get(v_a_1279_, 0);
lean_inc_n(v_fvarId_1280_, 2);
v___x_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_fvarId_1280_);
v___x_1282_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_fvarId_1280_, v_selfSets_1266_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1296_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1296_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_mk_empty_array_with_capacity(v___x_1287_);
v___x_1289_ = lean_array_push(v___x_1288_, v___x_1281_);
v___x_1290_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1290_, 0, v_contJpId_1265_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1276_, v_a_1283_, v___x_1290_);
lean_dec(v_a_1283_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_a_1279_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1292_);
v___x_1294_ = v___x_1285_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_selfSets_1266_);
lean_dec(v_contJpId_1265_);
v_a_1297_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1278_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1278_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec_ref(v_selfSets_1266_);
lean_dec(v_contJpId_1265_);
lean_dec_ref(v_args_1264_);
lean_dec_ref(v_info_1263_);
lean_dec_ref(v_decl_1262_);
v_a_1305_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1273_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1273_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(lean_object* v_decl_1313_, lean_object* v_info_1314_, lean_object* v_args_1315_, lean_object* v_contJpId_1316_, lean_object* v_selfSets_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1313_, v_info_1314_, v_args_1315_, v_contJpId_1316_, v_selfSets_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(lean_object* v_alt_1324_, lean_object* v_f_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___y_1332_; 
switch(lean_obj_tag(v_alt_1324_))
{
case 0:
{
lean_object* v_code_1351_; 
v_code_1351_ = lean_ctor_get(v_alt_1324_, 2);
lean_inc_ref(v_code_1351_);
v___y_1332_ = v_code_1351_;
goto v___jp_1331_;
}
case 1:
{
lean_object* v_code_1352_; 
v_code_1352_ = lean_ctor_get(v_alt_1324_, 1);
lean_inc_ref(v_code_1352_);
v___y_1332_ = v_code_1352_;
goto v___jp_1331_;
}
default: 
{
lean_object* v_code_1353_; 
v_code_1353_ = lean_ctor_get(v_alt_1324_, 0);
lean_inc_ref(v_code_1353_);
v___y_1332_ = v_code_1353_;
goto v___jp_1331_;
}
}
v___jp_1331_:
{
lean_object* v___x_1333_; 
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
v___x_1333_ = lean_apply_6(v_f_1325_, v___y_1332_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, lean_box(0));
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1342_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1342_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1342_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1324_, v_a_1334_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1338_);
v___x_1340_ = v___x_1336_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v_alt_1324_);
v_a_1343_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1333_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1333_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(lean_object* v_alt_1354_, lean_object* v_f_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1354_, v_f_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(uint8_t v_pu_1362_, lean_object* v_alt_1363_, lean_object* v_f_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1363_, v_f_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(lean_object* v_pu_1371_, lean_object* v_alt_1372_, lean_object* v_f_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
uint8_t v_pu_boxed_1379_; lean_object* v_res_1380_; 
v_pu_boxed_1379_ = lean_unbox(v_pu_1371_);
v_res_1380_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(v_pu_boxed_1379_, v_alt_1372_, v_f_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1380_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0(void){
_start:
{
uint8_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = 1;
v___x_1382_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object* v_msg_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_toApplicative_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1424_; 
v___x_1389_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_1390_ = l_StateRefT_x27_instMonad___redArg(v___x_1389_);
v_toApplicative_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v___x_1390_, 1);
lean_dec(v_unused_1425_);
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1424_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_toApplicative_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1424_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v_toFunctor_1395_; lean_object* v_toSeq_1396_; lean_object* v_toSeqLeft_1397_; lean_object* v_toSeqRight_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1422_; 
v_toFunctor_1395_ = lean_ctor_get(v_toApplicative_1391_, 0);
v_toSeq_1396_ = lean_ctor_get(v_toApplicative_1391_, 2);
v_toSeqLeft_1397_ = lean_ctor_get(v_toApplicative_1391_, 3);
v_toSeqRight_1398_ = lean_ctor_get(v_toApplicative_1391_, 4);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_toApplicative_1391_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v_toApplicative_1391_, 1);
lean_dec(v_unused_1423_);
v___x_1400_ = v_toApplicative_1391_;
v_isShared_1401_ = v_isSharedCheck_1422_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_toSeqRight_1398_);
lean_inc(v_toSeqLeft_1397_);
lean_inc(v_toSeq_1396_);
lean_inc(v_toFunctor_1395_);
lean_dec(v_toApplicative_1391_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1422_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___f_1402_; lean_object* v___f_1403_; lean_object* v___f_1404_; lean_object* v___f_1405_; lean_object* v___x_1406_; lean_object* v___f_1407_; lean_object* v___f_1408_; lean_object* v___f_1409_; lean_object* v___x_1411_; 
v___f_1402_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_1403_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1395_);
v___f_1404_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1404_, 0, v_toFunctor_1395_);
v___f_1405_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1405_, 0, v_toFunctor_1395_);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___f_1404_);
lean_ctor_set(v___x_1406_, 1, v___f_1405_);
v___f_1407_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1407_, 0, v_toSeqRight_1398_);
v___f_1408_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1408_, 0, v_toSeqLeft_1397_);
v___f_1409_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1409_, 0, v_toSeq_1396_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 4, v___f_1407_);
lean_ctor_set(v___x_1400_, 3, v___f_1408_);
lean_ctor_set(v___x_1400_, 2, v___f_1409_);
lean_ctor_set(v___x_1400_, 1, v___f_1402_);
lean_ctor_set(v___x_1400_, 0, v___x_1406_);
v___x_1411_ = v___x_1400_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___f_1402_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v___f_1409_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v___f_1408_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v___f_1407_);
v___x_1411_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1413_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v___f_1403_);
lean_ctor_set(v___x_1393_, 0, v___x_1411_);
v___x_1413_ = v___x_1393_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v___f_1403_);
v___x_1413_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___f_1417_; lean_object* v___x_7080__overap_1418_; lean_object* v___x_1419_; 
v___x_1414_ = l_StateRefT_x27_instMonad___redArg(v___x_1413_);
v___x_1415_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0);
v___x_1416_ = l_instInhabitedOfMonad___redArg(v___x_1414_, v___x_1415_);
v___f_1417_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1417_, 0, v___x_1416_);
v___x_7080__overap_1418_ = lean_panic_fn_borrowed(v___f_1417_, v_msg_1383_);
lean_dec_ref(v___f_1417_);
lean_inc(v___y_1387_);
lean_inc_ref(v___y_1386_);
lean_inc(v___y_1385_);
lean_inc_ref(v___y_1384_);
v___x_1419_ = lean_apply_5(v___x_7080__overap_1418_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, lean_box(0));
return v___x_1419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object* v_msg_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v_msg_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1432_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = lean_box(0);
v___x_1440_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3));
v___x_1441_ = l_Lean_Expr_const___override(v___x_1440_, v___x_1439_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object* v_resetTokenId_1442_, lean_object* v_origAllocId_1443_, lean_object* v_isSharedId_1444_, lean_object* v_resultType_1445_, lean_object* v_x_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(v_resetTokenId_1442_, v_origAllocId_1443_, v_isSharedId_1444_, v_resultType_1445_, v_x_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object* v_resetTokenId_1453_, lean_object* v_origAllocId_1454_, lean_object* v_isSharedId_1455_, lean_object* v_resultType_1456_, lean_object* v_i_1457_, lean_object* v_as_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = lean_array_get_size(v_as_1458_);
v___x_1465_ = lean_nat_dec_lt(v_i_1457_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; 
lean_dec(v_i_1457_);
lean_dec_ref(v_resultType_1456_);
lean_dec(v_isSharedId_1455_);
lean_dec(v_origAllocId_1454_);
lean_dec(v_resetTokenId_1453_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_as_1458_);
return v___x_1466_;
}
else
{
lean_object* v___f_1467_; lean_object* v_a_1468_; lean_object* v___x_1469_; 
lean_inc_ref(v_resultType_1456_);
lean_inc(v_isSharedId_1455_);
lean_inc(v_origAllocId_1454_);
lean_inc(v_resetTokenId_1453_);
v___f_1467_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1467_, 0, v_resetTokenId_1453_);
lean_closure_set(v___f_1467_, 1, v_origAllocId_1454_);
lean_closure_set(v___f_1467_, 2, v_isSharedId_1455_);
lean_closure_set(v___f_1467_, 3, v_resultType_1456_);
v_a_1468_ = lean_array_fget_borrowed(v_as_1458_, v_i_1457_);
lean_inc(v_a_1468_);
v___x_1469_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_1468_, v___f_1467_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; size_t v___x_1471_; size_t v___x_1472_; uint8_t v___x_1473_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref(v___x_1469_);
v___x_1471_ = lean_ptr_addr(v_a_1468_);
v___x_1472_ = lean_ptr_addr(v_a_1470_);
v___x_1473_ = lean_usize_dec_eq(v___x_1471_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_unsigned_to_nat(1u);
v___x_1475_ = lean_nat_add(v_i_1457_, v___x_1474_);
v___x_1476_ = lean_array_fset(v_as_1458_, v_i_1457_, v_a_1470_);
lean_dec(v_i_1457_);
v_i_1457_ = v___x_1475_;
v_as_1458_ = v___x_1476_;
goto _start;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v_a_1470_);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_add(v_i_1457_, v___x_1478_);
lean_dec(v_i_1457_);
v_i_1457_ = v___x_1479_;
goto _start;
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v_as_1458_);
lean_dec(v_i_1457_);
lean_dec_ref(v_resultType_1456_);
lean_dec(v_isSharedId_1455_);
lean_dec(v_origAllocId_1454_);
lean_dec(v_resetTokenId_1453_);
v_a_1481_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1469_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1469_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1491_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6));
v___x_1492_ = lean_unsigned_to_nat(6u);
v___x_1493_ = lean_unsigned_to_nat(208u);
v___x_1494_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5));
v___x_1495_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1));
v___x_1496_ = l_mkPanicMessageWithDecl(v___x_1495_, v___x_1494_, v___x_1493_, v___x_1492_, v___x_1491_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object* v_resetTokenId_1497_, lean_object* v_code_1498_, lean_object* v_origAllocId_1499_, lean_object* v_isSharedId_1500_, lean_object* v_currentRetType_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
switch(lean_obj_tag(v_code_1498_))
{
case 0:
{
lean_object* v_decl_1507_; lean_object* v_value_1508_; 
v_decl_1507_ = lean_ctor_get(v_code_1498_, 0);
v_value_1508_ = lean_ctor_get(v_decl_1507_, 3);
lean_inc(v_value_1508_);
if (lean_obj_tag(v_value_1508_) == 12)
{
lean_object* v_k_1509_; lean_object* v_fvarId_1510_; lean_object* v_binderName_1511_; lean_object* v_type_1512_; lean_object* v_var_1513_; lean_object* v_i_1514_; uint8_t v_updateHeader_1515_; lean_object* v_args_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1632_; 
v_k_1509_ = lean_ctor_get(v_code_1498_, 1);
v_fvarId_1510_ = lean_ctor_get(v_decl_1507_, 0);
v_binderName_1511_ = lean_ctor_get(v_decl_1507_, 1);
v_type_1512_ = lean_ctor_get(v_decl_1507_, 2);
v_var_1513_ = lean_ctor_get(v_value_1508_, 0);
v_i_1514_ = lean_ctor_get(v_value_1508_, 1);
v_updateHeader_1515_ = lean_ctor_get_uint8(v_value_1508_, sizeof(void*)*3);
v_args_1516_ = lean_ctor_get(v_value_1508_, 2);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_value_1508_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1518_ = v_value_1508_;
v_isShared_1519_ = v_isSharedCheck_1632_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_args_1516_);
lean_inc(v_i_1514_);
lean_inc(v_var_1513_);
lean_dec(v_value_1508_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1632_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint8_t v___x_1520_; 
v___x_1520_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1497_, v_var_1513_);
lean_dec(v_var_1513_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; 
lean_del_object(v___x_1518_);
lean_dec_ref(v_args_1516_);
lean_dec_ref(v_i_1514_);
lean_inc_ref(v_k_1509_);
v___x_1521_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_k_1509_, v_origAllocId_1499_, v_isSharedId_1500_, v_currentRetType_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1544_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1544_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1544_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
size_t v___x_1526_; size_t v___x_1527_; uint8_t v___x_1528_; 
v___x_1526_ = lean_ptr_addr(v_k_1509_);
v___x_1527_ = lean_ptr_addr(v_a_1522_);
v___x_1528_ = lean_usize_dec_eq(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1538_; 
lean_inc_ref(v_decl_1507_);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; lean_object* v_unused_1540_; 
v_unused_1539_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1540_);
v___x_1530_ = v_code_1498_;
v_isShared_1531_ = v_isSharedCheck_1538_;
goto v_resetjp_1529_;
}
else
{
lean_dec(v_code_1498_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1538_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v_a_1522_);
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_decl_1507_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_a_1522_);
v___x_1533_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1533_);
v___x_1535_ = v___x_1524_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v___x_1542_; 
lean_dec(v_a_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v_code_1498_);
v___x_1542_ = v___x_1524_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_code_1498_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_dec_ref(v_code_1498_);
return v___x_1521_;
}
}
else
{
lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1629_; 
lean_inc_ref(v_k_1509_);
lean_inc_ref(v_decl_1507_);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; lean_object* v_unused_1631_; 
v_unused_1630_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1630_);
v_unused_1631_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1631_);
v___x_1546_ = v_code_1498_;
v_isShared_1547_ = v_isSharedCheck_1629_;
goto v_resetjp_1545_;
}
else
{
lean_dec(v_code_1498_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1629_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; 
v___x_1548_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_fvarId_1510_, v_k_1509_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v_fst_1550_; lean_object* v_snd_1551_; lean_object* v___x_1552_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1548_);
v_fst_1550_ = lean_ctor_get(v_a_1549_, 0);
lean_inc(v_fst_1550_);
v_snd_1551_ = lean_ctor_get(v_a_1549_, 1);
lean_inc(v_snd_1551_);
lean_dec(v_a_1549_);
v___x_1552_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_origAllocId_1499_, v_fst_1550_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
lean_dec(v_fst_1550_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v_fst_1554_; lean_object* v_snd_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
v_fst_1554_ = lean_ctor_get(v_a_1553_, 0);
lean_inc(v_fst_1554_);
v_snd_1555_ = lean_ctor_get(v_a_1553_, 1);
lean_inc(v_snd_1555_);
lean_dec(v_a_1553_);
v___x_1556_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1));
v___x_1557_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1556_, v_a_1503_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1563_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = 1;
v___x_1560_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1559_, v_snd_1555_, v_snd_1551_);
lean_dec(v_snd_1555_);
v___x_1561_ = 0;
lean_inc_ref(v_type_1512_);
lean_inc(v_binderName_1511_);
lean_inc(v_fvarId_1510_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 0);
lean_ctor_set(v___x_1518_, 2, v_type_1512_);
lean_ctor_set(v___x_1518_, 1, v_binderName_1511_);
lean_ctor_set(v___x_1518_, 0, v_fvarId_1510_);
v___x_1563_ = v___x_1518_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_fvarId_1510_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_binderName_1511_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_type_1512_);
v___x_1563_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*3, v___x_1561_);
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_mk_empty_array_with_capacity(v___x_1564_);
v___x_1566_ = lean_array_push(v___x_1565_, v___x_1563_);
lean_inc_ref(v_currentRetType_1501_);
v___x_1567_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_1559_, v_a_1558_, v_currentRetType_1501_, v___x_1566_, v___x_1560_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_fvarId_1569_; lean_object* v___x_1570_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1567_);
v_fvarId_1569_ = lean_ctor_get(v_a_1568_, 0);
lean_inc(v_fvarId_1569_);
lean_inc_ref(v_args_1516_);
lean_inc_ref(v_i_1514_);
lean_inc_ref(v_decl_1507_);
v___x_1570_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1507_, v_i_1514_, v_args_1516_, v_fvarId_1569_, v_fst_1554_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref(v___x_1570_);
lean_inc(v_fvarId_1569_);
v___x_1572_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1497_, v_i_1514_, v_updateHeader_1515_, v_args_1516_, v_fvarId_1569_, v_origAllocId_1499_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
lean_dec(v_origAllocId_1499_);
lean_dec_ref(v_args_1516_);
lean_dec_ref(v_i_1514_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_1559_, v_decl_1507_, v_a_1503_);
lean_dec_ref(v_decl_1507_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec_ref(v___x_1574_);
v___x_1575_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_1576_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_isSharedId_1500_, v___x_1575_, v_currentRetType_1501_, v_a_1571_, v_a_1573_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1587_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1587_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1587_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 2);
lean_ctor_set(v___x_1546_, 1, v_a_1577_);
lean_ctor_set(v___x_1546_, 0, v_a_1568_);
v___x_1582_ = v___x_1546_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1568_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1582_);
v___x_1584_ = v___x_1579_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_dec(v_a_1568_);
lean_del_object(v___x_1546_);
return v___x_1576_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec(v_a_1573_);
lean_dec(v_a_1571_);
lean_dec(v_a_1568_);
lean_del_object(v___x_1546_);
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
v_a_1588_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1574_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1574_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_dec(v_a_1571_);
lean_dec(v_a_1568_);
lean_del_object(v___x_1546_);
lean_dec_ref(v_decl_1507_);
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
return v___x_1572_;
}
}
else
{
lean_dec(v_a_1568_);
lean_del_object(v___x_1546_);
lean_dec_ref(v_args_1516_);
lean_dec_ref(v_i_1514_);
lean_dec_ref(v_decl_1507_);
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
lean_dec(v_origAllocId_1499_);
lean_dec(v_resetTokenId_1497_);
return v___x_1570_;
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_fst_1554_);
lean_del_object(v___x_1546_);
lean_dec_ref(v_args_1516_);
lean_dec_ref(v_i_1514_);
lean_dec_ref(v_decl_1507_);
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
lean_dec(v_origAllocId_1499_);
lean_dec(v_resetTokenId_1497_);
v_a_1596_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1567_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1567_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_snd_1555_);
lean_dec(v_fst_1554_);
lean_dec(v_snd_1551_);
lean_del_object(v___x_1546_);
lean_del_object(v___x_1518_);
lean_dec_ref(v_args_1516_);
lean_dec_ref(v_i_1514_);
lean_dec_ref(v_decl_1507_);
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
lean_dec(v_origAllocId_1499_);
lean_dec(v_resetTokenId_1497_);
v_a_1605_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1557_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1557_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v_snd_1551_);
lean_del_object(v___x_1546_);
lean_del_object(v___x_1518_);
lean_dec_ref(v_args_1516_);
lean_dec_ref(v_i_1514_);
lean_dec_ref(v_decl_1507_);
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
lean_dec(v_origAllocId_1499_);
lean_dec(v_resetTokenId_1497_);
v_a_1613_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1552_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1552_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
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
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_del_object(v___x_1546_);
lean_del_object(v___x_1518_);
lean_dec_ref(v_args_1516_);
lean_dec_ref(v_i_1514_);
lean_dec_ref(v_decl_1507_);
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
lean_dec(v_origAllocId_1499_);
lean_dec(v_resetTokenId_1497_);
v_a_1621_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1548_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1548_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
}
else
{
lean_object* v_k_1633_; lean_object* v___x_1634_; 
lean_dec(v_value_1508_);
v_k_1633_ = lean_ctor_get(v_code_1498_, 1);
lean_inc_ref(v_k_1633_);
v___x_1634_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_k_1633_, v_origAllocId_1499_, v_isSharedId_1500_, v_currentRetType_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1657_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1657_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1657_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
size_t v___x_1639_; size_t v___x_1640_; uint8_t v___x_1641_; 
v___x_1639_ = lean_ptr_addr(v_k_1633_);
v___x_1640_ = lean_ptr_addr(v_a_1635_);
v___x_1641_ = lean_usize_dec_eq(v___x_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1651_; 
lean_inc_ref(v_decl_1507_);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; lean_object* v_unused_1653_; 
v_unused_1652_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1652_);
v_unused_1653_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1653_);
v___x_1643_ = v_code_1498_;
v_isShared_1644_ = v_isSharedCheck_1651_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v_code_1498_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1651_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v_a_1635_);
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_decl_1507_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_a_1635_);
v___x_1646_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1648_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1646_);
v___x_1648_ = v___x_1637_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v___x_1655_; 
lean_dec(v_a_1635_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v_code_1498_);
v___x_1655_ = v___x_1637_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_code_1498_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_dec_ref(v_code_1498_);
return v___x_1634_;
}
}
}
case 2:
{
lean_object* v_decl_1658_; lean_object* v_k_1659_; lean_object* v_params_1660_; lean_object* v_type_1661_; lean_object* v_value_1662_; lean_object* v___x_1663_; 
v_decl_1658_ = lean_ctor_get(v_code_1498_, 0);
v_k_1659_ = lean_ctor_get(v_code_1498_, 1);
v_params_1660_ = lean_ctor_get(v_decl_1658_, 2);
v_type_1661_ = lean_ctor_get(v_decl_1658_, 3);
v_value_1662_ = lean_ctor_get(v_decl_1658_, 4);
lean_inc_ref(v_type_1661_);
lean_inc(v_isSharedId_1500_);
lean_inc(v_origAllocId_1499_);
lean_inc_ref(v_value_1662_);
lean_inc(v_resetTokenId_1497_);
v___x_1663_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_value_1662_, v_origAllocId_1499_, v_isSharedId_1500_, v_type_1661_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = 1;
lean_inc_ref(v_params_1660_);
lean_inc_ref(v_type_1661_);
lean_inc_ref(v_decl_1658_);
v___x_1666_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1665_, v_decl_1658_, v_type_1661_, v_params_1660_, v_a_1664_, v_a_1503_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v___x_1666_);
lean_inc_ref(v_k_1659_);
v___x_1668_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_k_1659_, v_origAllocId_1499_, v_isSharedId_1500_, v_currentRetType_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1696_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1696_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1696_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
uint8_t v___y_1674_; size_t v___x_1690_; size_t v___x_1691_; uint8_t v___x_1692_; 
v___x_1690_ = lean_ptr_addr(v_k_1659_);
v___x_1691_ = lean_ptr_addr(v_a_1669_);
v___x_1692_ = lean_usize_dec_eq(v___x_1690_, v___x_1691_);
if (v___x_1692_ == 0)
{
v___y_1674_ = v___x_1692_;
goto v___jp_1673_;
}
else
{
size_t v___x_1693_; size_t v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = lean_ptr_addr(v_decl_1658_);
v___x_1694_ = lean_ptr_addr(v_a_1667_);
v___x_1695_ = lean_usize_dec_eq(v___x_1693_, v___x_1694_);
v___y_1674_ = v___x_1695_;
goto v___jp_1673_;
}
v___jp_1673_:
{
if (v___y_1674_ == 0)
{
lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1684_; 
v_isSharedCheck_1684_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; lean_object* v_unused_1686_; 
v_unused_1685_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1686_);
v___x_1676_ = v_code_1498_;
v_isShared_1677_ = v_isSharedCheck_1684_;
goto v_resetjp_1675_;
}
else
{
lean_dec(v_code_1498_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1684_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v_a_1669_);
lean_ctor_set(v___x_1676_, 0, v_a_1667_);
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1667_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_a_1669_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1679_);
v___x_1681_ = v___x_1671_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v___x_1688_; 
lean_dec(v_a_1669_);
lean_dec(v_a_1667_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v_code_1498_);
v___x_1688_ = v___x_1671_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_code_1498_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
else
{
lean_dec(v_a_1667_);
lean_dec_ref(v_code_1498_);
return v___x_1668_;
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_code_1498_);
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
lean_dec(v_origAllocId_1499_);
lean_dec(v_resetTokenId_1497_);
v_a_1697_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1666_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1666_);
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
else
{
lean_dec_ref(v_code_1498_);
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
lean_dec(v_origAllocId_1499_);
lean_dec(v_resetTokenId_1497_);
return v___x_1663_;
}
}
case 4:
{
lean_object* v_cases_1705_; lean_object* v_typeName_1706_; lean_object* v_resultType_1707_; lean_object* v_discr_1708_; lean_object* v_alts_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1748_; 
lean_dec_ref(v_currentRetType_1501_);
v_cases_1705_ = lean_ctor_get(v_code_1498_, 0);
lean_inc_ref(v_cases_1705_);
v_typeName_1706_ = lean_ctor_get(v_cases_1705_, 0);
v_resultType_1707_ = lean_ctor_get(v_cases_1705_, 1);
v_discr_1708_ = lean_ctor_get(v_cases_1705_, 2);
v_alts_1709_ = lean_ctor_get(v_cases_1705_, 3);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_cases_1705_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1711_ = v_cases_1705_;
v_isShared_1712_ = v_isSharedCheck_1748_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_alts_1709_);
lean_inc(v_discr_1708_);
lean_inc(v_resultType_1707_);
lean_inc(v_typeName_1706_);
lean_dec(v_cases_1705_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1748_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1709_);
lean_inc_ref(v_resultType_1707_);
v___x_1714_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_1497_, v_origAllocId_1499_, v_isSharedId_1500_, v_resultType_1707_, v___x_1713_, v_alts_1709_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1739_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1739_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1739_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
size_t v___x_1719_; size_t v___x_1720_; uint8_t v___x_1721_; 
v___x_1719_ = lean_ptr_addr(v_alts_1709_);
lean_dec_ref(v_alts_1709_);
v___x_1720_ = lean_ptr_addr(v_a_1715_);
v___x_1721_ = lean_usize_dec_eq(v___x_1719_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1734_; 
v_isSharedCheck_1734_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1735_);
v___x_1723_ = v_code_1498_;
v_isShared_1724_ = v_isSharedCheck_1734_;
goto v_resetjp_1722_;
}
else
{
lean_dec(v_code_1498_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1734_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 3, v_a_1715_);
v___x_1726_ = v___x_1711_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_typeName_1706_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_resultType_1707_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_discr_1708_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v_a_1715_);
v___x_1726_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1728_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1726_);
v___x_1728_ = v___x_1723_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1730_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1728_);
v___x_1730_ = v___x_1717_;
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
}
else
{
lean_object* v___x_1737_; 
lean_dec(v_a_1715_);
lean_del_object(v___x_1711_);
lean_dec(v_discr_1708_);
lean_dec_ref(v_resultType_1707_);
lean_dec(v_typeName_1706_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v_code_1498_);
v___x_1737_ = v___x_1717_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_code_1498_);
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
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_del_object(v___x_1711_);
lean_dec_ref(v_alts_1709_);
lean_dec(v_discr_1708_);
lean_dec_ref(v_resultType_1707_);
lean_dec(v_typeName_1706_);
lean_dec_ref(v_code_1498_);
v_a_1740_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1714_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1714_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1749_; lean_object* v_i_1750_; lean_object* v_y_1751_; lean_object* v_k_1752_; lean_object* v___x_1753_; 
v_fvarId_1749_ = lean_ctor_get(v_code_1498_, 0);
v_i_1750_ = lean_ctor_get(v_code_1498_, 1);
v_y_1751_ = lean_ctor_get(v_code_1498_, 2);
v_k_1752_ = lean_ctor_get(v_code_1498_, 3);
lean_inc_ref(v_k_1752_);
v___x_1753_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_k_1752_, v_origAllocId_1499_, v_isSharedId_1500_, v_currentRetType_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1778_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1778_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1778_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
size_t v___x_1758_; size_t v___x_1759_; uint8_t v___x_1760_; 
v___x_1758_ = lean_ptr_addr(v_k_1752_);
v___x_1759_ = lean_ptr_addr(v_a_1754_);
v___x_1760_ = lean_usize_dec_eq(v___x_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1770_; 
lean_inc(v_y_1751_);
lean_inc(v_i_1750_);
lean_inc(v_fvarId_1749_);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; lean_object* v_unused_1772_; lean_object* v_unused_1773_; lean_object* v_unused_1774_; 
v_unused_1771_ = lean_ctor_get(v_code_1498_, 3);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v_code_1498_, 2);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1774_);
v___x_1762_ = v_code_1498_;
v_isShared_1763_ = v_isSharedCheck_1770_;
goto v_resetjp_1761_;
}
else
{
lean_dec(v_code_1498_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1770_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 3, v_a_1754_);
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_fvarId_1749_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_i_1750_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_y_1751_);
lean_ctor_set(v_reuseFailAlloc_1769_, 3, v_a_1754_);
v___x_1765_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1767_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1765_);
v___x_1767_ = v___x_1756_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v___x_1776_; 
lean_dec(v_a_1754_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v_code_1498_);
v___x_1776_ = v___x_1756_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_code_1498_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_dec_ref(v_code_1498_);
return v___x_1753_;
}
}
case 8:
{
lean_object* v_fvarId_1779_; lean_object* v_i_1780_; lean_object* v_y_1781_; lean_object* v_k_1782_; lean_object* v___x_1783_; 
v_fvarId_1779_ = lean_ctor_get(v_code_1498_, 0);
v_i_1780_ = lean_ctor_get(v_code_1498_, 1);
v_y_1781_ = lean_ctor_get(v_code_1498_, 2);
v_k_1782_ = lean_ctor_get(v_code_1498_, 3);
lean_inc_ref(v_k_1782_);
v___x_1783_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_k_1782_, v_origAllocId_1499_, v_isSharedId_1500_, v_currentRetType_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1808_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1808_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1808_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
size_t v___x_1788_; size_t v___x_1789_; uint8_t v___x_1790_; 
v___x_1788_ = lean_ptr_addr(v_k_1782_);
v___x_1789_ = lean_ptr_addr(v_a_1784_);
v___x_1790_ = lean_usize_dec_eq(v___x_1788_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1800_; 
lean_inc(v_y_1781_);
lean_inc(v_i_1780_);
lean_inc(v_fvarId_1779_);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; lean_object* v_unused_1802_; lean_object* v_unused_1803_; lean_object* v_unused_1804_; 
v_unused_1801_ = lean_ctor_get(v_code_1498_, 3);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_code_1498_, 2);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1804_);
v___x_1792_ = v_code_1498_;
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
else
{
lean_dec(v_code_1498_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 3, v_a_1784_);
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_fvarId_1779_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_i_1780_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_y_1781_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_a_1784_);
v___x_1795_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1795_);
v___x_1797_ = v___x_1786_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v___x_1806_; 
lean_dec(v_a_1784_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v_code_1498_);
v___x_1806_ = v___x_1786_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_code_1498_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_dec_ref(v_code_1498_);
return v___x_1783_;
}
}
case 9:
{
lean_object* v_fvarId_1809_; lean_object* v_i_1810_; lean_object* v_offset_1811_; lean_object* v_y_1812_; lean_object* v_ty_1813_; lean_object* v_k_1814_; lean_object* v___x_1815_; 
v_fvarId_1809_ = lean_ctor_get(v_code_1498_, 0);
v_i_1810_ = lean_ctor_get(v_code_1498_, 1);
v_offset_1811_ = lean_ctor_get(v_code_1498_, 2);
v_y_1812_ = lean_ctor_get(v_code_1498_, 3);
v_ty_1813_ = lean_ctor_get(v_code_1498_, 4);
v_k_1814_ = lean_ctor_get(v_code_1498_, 5);
lean_inc_ref(v_k_1814_);
v___x_1815_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_k_1814_, v_origAllocId_1499_, v_isSharedId_1500_, v_currentRetType_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1842_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1842_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1842_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
size_t v___x_1820_; size_t v___x_1821_; uint8_t v___x_1822_; 
v___x_1820_ = lean_ptr_addr(v_k_1814_);
v___x_1821_ = lean_ptr_addr(v_a_1816_);
v___x_1822_ = lean_usize_dec_eq(v___x_1820_, v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1832_; 
lean_inc_ref(v_ty_1813_);
lean_inc(v_y_1812_);
lean_inc(v_offset_1811_);
lean_inc(v_i_1810_);
lean_inc(v_fvarId_1809_);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; lean_object* v_unused_1834_; lean_object* v_unused_1835_; lean_object* v_unused_1836_; lean_object* v_unused_1837_; lean_object* v_unused_1838_; 
v_unused_1833_ = lean_ctor_get(v_code_1498_, 5);
lean_dec(v_unused_1833_);
v_unused_1834_ = lean_ctor_get(v_code_1498_, 4);
lean_dec(v_unused_1834_);
v_unused_1835_ = lean_ctor_get(v_code_1498_, 3);
lean_dec(v_unused_1835_);
v_unused_1836_ = lean_ctor_get(v_code_1498_, 2);
lean_dec(v_unused_1836_);
v_unused_1837_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1838_);
v___x_1824_ = v_code_1498_;
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
else
{
lean_dec(v_code_1498_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 5, v_a_1816_);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_fvarId_1809_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_i_1810_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_offset_1811_);
lean_ctor_set(v_reuseFailAlloc_1831_, 3, v_y_1812_);
lean_ctor_set(v_reuseFailAlloc_1831_, 4, v_ty_1813_);
lean_ctor_set(v_reuseFailAlloc_1831_, 5, v_a_1816_);
v___x_1827_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1829_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1827_);
v___x_1829_ = v___x_1818_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v___x_1840_; 
lean_dec(v_a_1816_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v_code_1498_);
v___x_1840_ = v___x_1818_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_code_1498_);
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
lean_dec_ref(v_code_1498_);
return v___x_1815_;
}
}
case 10:
{
lean_object* v_fvarId_1843_; lean_object* v_cidx_1844_; lean_object* v_k_1845_; lean_object* v___x_1846_; 
v_fvarId_1843_ = lean_ctor_get(v_code_1498_, 0);
v_cidx_1844_ = lean_ctor_get(v_code_1498_, 1);
v_k_1845_ = lean_ctor_get(v_code_1498_, 2);
lean_inc_ref(v_k_1845_);
v___x_1846_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_k_1845_, v_origAllocId_1499_, v_isSharedId_1500_, v_currentRetType_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1870_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1870_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1870_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
size_t v___x_1851_; size_t v___x_1852_; uint8_t v___x_1853_; 
v___x_1851_ = lean_ptr_addr(v_k_1845_);
v___x_1852_ = lean_ptr_addr(v_a_1847_);
v___x_1853_ = lean_usize_dec_eq(v___x_1851_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1863_; 
lean_inc(v_cidx_1844_);
lean_inc(v_fvarId_1843_);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; lean_object* v_unused_1865_; lean_object* v_unused_1866_; 
v_unused_1864_ = lean_ctor_get(v_code_1498_, 2);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1866_);
v___x_1855_ = v_code_1498_;
v_isShared_1856_ = v_isSharedCheck_1863_;
goto v_resetjp_1854_;
}
else
{
lean_dec(v_code_1498_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1863_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 2, v_a_1847_);
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_fvarId_1843_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_cidx_1844_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v_a_1847_);
v___x_1858_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1860_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1858_);
v___x_1860_ = v___x_1849_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_1868_; 
lean_dec(v_a_1847_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_code_1498_);
v___x_1868_ = v___x_1849_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_code_1498_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_dec_ref(v_code_1498_);
return v___x_1846_;
}
}
case 11:
{
lean_object* v_fvarId_1871_; lean_object* v_n_1872_; uint8_t v_check_1873_; uint8_t v_persistent_1874_; lean_object* v_k_1875_; lean_object* v___x_1876_; 
v_fvarId_1871_ = lean_ctor_get(v_code_1498_, 0);
v_n_1872_ = lean_ctor_get(v_code_1498_, 1);
v_check_1873_ = lean_ctor_get_uint8(v_code_1498_, sizeof(void*)*3);
v_persistent_1874_ = lean_ctor_get_uint8(v_code_1498_, sizeof(void*)*3 + 1);
v_k_1875_ = lean_ctor_get(v_code_1498_, 2);
lean_inc_ref(v_k_1875_);
v___x_1876_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_k_1875_, v_origAllocId_1499_, v_isSharedId_1500_, v_currentRetType_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1900_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1900_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1900_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
size_t v___x_1881_; size_t v___x_1882_; uint8_t v___x_1883_; 
v___x_1881_ = lean_ptr_addr(v_k_1875_);
v___x_1882_ = lean_ptr_addr(v_a_1877_);
v___x_1883_ = lean_usize_dec_eq(v___x_1881_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1893_; 
lean_inc(v_n_1872_);
lean_inc(v_fvarId_1871_);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; lean_object* v_unused_1895_; lean_object* v_unused_1896_; 
v_unused_1894_ = lean_ctor_get(v_code_1498_, 2);
lean_dec(v_unused_1894_);
v_unused_1895_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1895_);
v_unused_1896_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1896_);
v___x_1885_ = v_code_1498_;
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
else
{
lean_dec(v_code_1498_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 2, v_a_1877_);
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_fvarId_1871_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_n_1872_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_a_1877_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*3, v_check_1873_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*3 + 1, v_persistent_1874_);
v___x_1888_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1888_);
v___x_1890_ = v___x_1879_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v___x_1898_; 
lean_dec(v_a_1877_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v_code_1498_);
v___x_1898_ = v___x_1879_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_code_1498_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_dec_ref(v_code_1498_);
return v___x_1876_;
}
}
case 12:
{
lean_object* v_fvarId_1901_; lean_object* v_n_1902_; uint8_t v_check_1903_; uint8_t v_persistent_1904_; lean_object* v_k_1905_; uint8_t v___x_1906_; 
v_fvarId_1901_ = lean_ctor_get(v_code_1498_, 0);
v_n_1902_ = lean_ctor_get(v_code_1498_, 1);
v_check_1903_ = lean_ctor_get_uint8(v_code_1498_, sizeof(void*)*3);
v_persistent_1904_ = lean_ctor_get_uint8(v_code_1498_, sizeof(void*)*3 + 1);
v_k_1905_ = lean_ctor_get(v_code_1498_, 2);
v___x_1906_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1497_, v_fvarId_1901_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
lean_inc_ref(v_k_1905_);
v___x_1907_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_k_1905_, v_origAllocId_1499_, v_isSharedId_1500_, v_currentRetType_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1931_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1931_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1931_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
size_t v___x_1912_; size_t v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = lean_ptr_addr(v_k_1905_);
v___x_1913_ = lean_ptr_addr(v_a_1908_);
v___x_1914_ = lean_usize_dec_eq(v___x_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1924_; 
lean_inc(v_n_1902_);
lean_inc(v_fvarId_1901_);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; lean_object* v_unused_1926_; lean_object* v_unused_1927_; 
v_unused_1925_ = lean_ctor_get(v_code_1498_, 2);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1927_);
v___x_1916_ = v_code_1498_;
v_isShared_1917_ = v_isSharedCheck_1924_;
goto v_resetjp_1915_;
}
else
{
lean_dec(v_code_1498_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1924_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 2, v_a_1908_);
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_fvarId_1901_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_n_1902_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_a_1908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*3, v_check_1903_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*3 + 1, v_persistent_1904_);
v___x_1919_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1921_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1919_);
v___x_1921_ = v___x_1910_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v___x_1929_; 
lean_dec(v_a_1908_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v_code_1498_);
v___x_1929_ = v___x_1910_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_code_1498_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_dec_ref(v_code_1498_);
return v___x_1907_;
}
}
else
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
lean_inc_ref(v_k_1905_);
lean_inc(v_n_1902_);
lean_dec_ref(v_code_1498_);
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
lean_dec(v_origAllocId_1499_);
v___x_1932_ = lean_unsigned_to_nat(1u);
v___x_1933_ = lean_nat_dec_eq(v_n_1902_, v___x_1932_);
lean_dec(v_n_1902_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_dec_ref(v_k_1905_);
lean_dec(v_resetTokenId_1497_);
v___x_1934_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7);
v___x_1935_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v___x_1934_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
return v___x_1935_;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1936_, 0, v_resetTokenId_1497_);
lean_ctor_set(v___x_1936_, 1, v_k_1905_);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
}
case 13:
{
lean_object* v_fvarId_1938_; lean_object* v_k_1939_; lean_object* v___x_1940_; 
v_fvarId_1938_ = lean_ctor_get(v_code_1498_, 0);
v_k_1939_ = lean_ctor_get(v_code_1498_, 1);
lean_inc_ref(v_k_1939_);
v___x_1940_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1497_, v_k_1939_, v_origAllocId_1499_, v_isSharedId_1500_, v_currentRetType_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1963_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1963_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1963_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
size_t v___x_1945_; size_t v___x_1946_; uint8_t v___x_1947_; 
v___x_1945_ = lean_ptr_addr(v_k_1939_);
v___x_1946_ = lean_ptr_addr(v_a_1941_);
v___x_1947_ = lean_usize_dec_eq(v___x_1945_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1957_; 
lean_inc(v_fvarId_1938_);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_code_1498_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; lean_object* v_unused_1959_; 
v_unused_1958_ = lean_ctor_get(v_code_1498_, 1);
lean_dec(v_unused_1958_);
v_unused_1959_ = lean_ctor_get(v_code_1498_, 0);
lean_dec(v_unused_1959_);
v___x_1949_ = v_code_1498_;
v_isShared_1950_ = v_isSharedCheck_1957_;
goto v_resetjp_1948_;
}
else
{
lean_dec(v_code_1498_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1957_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v_a_1941_);
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_fvarId_1938_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_a_1941_);
v___x_1952_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1952_);
v___x_1954_ = v___x_1943_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
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
lean_object* v___x_1961_; 
lean_dec(v_a_1941_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v_code_1498_);
v___x_1961_ = v___x_1943_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_code_1498_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_dec_ref(v_code_1498_);
return v___x_1940_;
}
}
default: 
{
lean_object* v___x_1964_; 
lean_dec_ref(v_currentRetType_1501_);
lean_dec(v_isSharedId_1500_);
lean_dec(v_origAllocId_1499_);
lean_dec(v_resetTokenId_1497_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v_code_1498_);
return v___x_1964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object* v_resetTokenId_1965_, lean_object* v_origAllocId_1966_, lean_object* v_isSharedId_1967_, lean_object* v_resultType_1968_, lean_object* v_x_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1965_, v_x_1969_, v_origAllocId_1966_, v_isSharedId_1967_, v_resultType_1968_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object* v_resetTokenId_1976_, lean_object* v_origAllocId_1977_, lean_object* v_isSharedId_1978_, lean_object* v_resultType_1979_, lean_object* v_i_1980_, lean_object* v_as_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_1976_, v_origAllocId_1977_, v_isSharedId_1978_, v_resultType_1979_, v_i_1980_, v_as_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object* v_resetTokenId_1988_, lean_object* v_code_1989_, lean_object* v_origAllocId_1990_, lean_object* v_isSharedId_1991_, lean_object* v_currentRetType_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1988_, v_code_1989_, v_origAllocId_1990_, v_isSharedId_1991_, v_currentRetType_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object* v_currentRetType_2008_, lean_object* v_ds_2009_, lean_object* v_decl_2010_, lean_object* v_nFields_2011_, lean_object* v_origAllocId_2012_, lean_object* v_k_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_2011_, v_origAllocId_2012_, v_ds_2009_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v_fst_2021_; lean_object* v_snd_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2143_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref(v___x_2019_);
v_fst_2021_ = lean_ctor_get(v_a_2020_, 0);
v_snd_2022_ = lean_ctor_get(v_a_2020_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_a_2020_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2024_ = v_a_2020_;
v_isShared_2025_ = v_isSharedCheck_2143_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_snd_2022_);
lean_inc(v_fst_2021_);
lean_dec(v_a_2020_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2143_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1));
v___x_2027_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2026_, v_a_2015_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; uint8_t v___x_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; lean_object* v___x_2032_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v___x_2029_ = 1;
v___x_2030_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_2031_ = 0;
v___x_2032_ = l_Lean_Compiler_LCNF_mkParam(v___x_2029_, v_a_2028_, v___x_2030_, v___x_2031_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v_fvarId_2034_; lean_object* v_binderName_2035_; lean_object* v_fvarId_2036_; lean_object* v___x_2037_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2032_);
v_fvarId_2034_ = lean_ctor_get(v_decl_2010_, 0);
v_binderName_2035_ = lean_ctor_get(v_decl_2010_, 1);
v_fvarId_2036_ = lean_ctor_get(v_a_2033_, 0);
lean_inc_ref(v_currentRetType_2008_);
lean_inc(v_fvarId_2036_);
lean_inc(v_origAllocId_2012_);
lean_inc(v_fvarId_2034_);
v___x_2037_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_fvarId_2034_, v_k_2013_, v_origAllocId_2012_, v_fvarId_2036_, v_currentRetType_2008_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_currentRetType_2008_);
v___x_2040_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_a_2038_, v___x_2039_, v_currentRetType_2008_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2126_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2126_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2126_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3));
v___x_2046_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2045_, v_a_2015_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref(v___x_2046_);
v___x_2048_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_binderName_2035_);
lean_inc(v_fvarId_2034_);
v___x_2049_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2049_, 0, v_fvarId_2034_);
lean_ctor_set(v___x_2049_, 1, v_binderName_2035_);
lean_ctor_set(v___x_2049_, 2, v___x_2048_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*3, v___x_2031_);
v___x_2050_ = lean_unsigned_to_nat(2u);
v___x_2051_ = lean_mk_empty_array_with_capacity(v___x_2050_);
v___x_2052_ = lean_array_push(v___x_2051_, v___x_2049_);
v___x_2053_ = lean_array_push(v___x_2052_, v_a_2033_);
lean_inc_ref(v_currentRetType_2008_);
v___x_2054_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_2029_, v_a_2047_, v_currentRetType_2008_, v___x_2053_, v_a_2041_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___x_2054_);
v___x_2056_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5));
v___x_2057_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2056_, v_a_2015_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2057_);
lean_inc(v_origAllocId_2012_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 15);
lean_ctor_set(v___x_2043_, 0, v_origAllocId_2012_);
v___x_2060_ = v___x_2043_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_origAllocId_2012_);
v___x_2060_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2029_, v_a_2058_, v___x_2030_, v___x_2060_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v_fvarId_2063_; lean_object* v_fvarId_2064_; lean_object* v___x_2065_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref(v___x_2061_);
v_fvarId_2063_ = lean_ctor_get(v_a_2055_, 0);
v_fvarId_2064_ = lean_ctor_get(v_a_2062_, 0);
lean_inc(v_fvarId_2064_);
lean_inc(v_fvarId_2063_);
lean_inc(v_origAllocId_2012_);
v___x_2065_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_2012_, v_snd_2022_, v_fvarId_2063_, v_fvarId_2064_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2065_);
lean_inc(v_fvarId_2064_);
lean_inc(v_fvarId_2063_);
v___x_2067_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_2012_, v_snd_2022_, v_fvarId_2063_, v_fvarId_2064_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_snd_2022_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2067_);
lean_inc(v_fvarId_2064_);
v___x_2069_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_fvarId_2064_, v___x_2030_, v_currentRetType_2008_, v_a_2066_, v_a_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref(v___x_2069_);
v___x_2071_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2029_, v_decl_2010_, v_a_2015_);
lean_dec_ref(v_decl_2010_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2083_; 
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v___x_2071_, 0);
lean_dec(v_unused_2084_);
v___x_2073_ = v___x_2071_;
v_isShared_2074_ = v_isSharedCheck_2083_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v___x_2071_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2083_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 1, v_a_2070_);
lean_ctor_set(v___x_2024_, 0, v_a_2062_);
v___x_2076_ = v___x_2024_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2062_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_a_2070_);
v___x_2076_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2077_, 0, v_a_2055_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2029_, v_fst_2021_, v___x_2077_);
lean_dec(v_fst_2021_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2078_);
v___x_2080_ = v___x_2073_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_a_2070_);
lean_dec(v_a_2062_);
lean_dec(v_a_2055_);
lean_del_object(v___x_2024_);
lean_dec(v_fst_2021_);
v_a_2085_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2071_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2071_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_dec(v_a_2062_);
lean_dec(v_a_2055_);
lean_del_object(v___x_2024_);
lean_dec(v_fst_2021_);
lean_dec_ref(v_decl_2010_);
return v___x_2069_;
}
}
else
{
lean_dec(v_a_2066_);
lean_dec(v_a_2062_);
lean_dec(v_a_2055_);
lean_del_object(v___x_2024_);
lean_dec(v_fst_2021_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
return v___x_2067_;
}
}
else
{
lean_dec(v_a_2062_);
lean_dec(v_a_2055_);
lean_del_object(v___x_2024_);
lean_dec(v_snd_2022_);
lean_dec(v_fst_2021_);
lean_dec(v_origAllocId_2012_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
return v___x_2065_;
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v_a_2055_);
lean_del_object(v___x_2024_);
lean_dec(v_snd_2022_);
lean_dec(v_fst_2021_);
lean_dec(v_origAllocId_2012_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
v_a_2093_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2061_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2061_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
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
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_a_2055_);
lean_del_object(v___x_2043_);
lean_del_object(v___x_2024_);
lean_dec(v_snd_2022_);
lean_dec(v_fst_2021_);
lean_dec(v_origAllocId_2012_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
v_a_2102_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2057_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2057_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_del_object(v___x_2043_);
lean_del_object(v___x_2024_);
lean_dec(v_snd_2022_);
lean_dec(v_fst_2021_);
lean_dec(v_origAllocId_2012_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
v_a_2110_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2054_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2054_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_del_object(v___x_2043_);
lean_dec(v_a_2041_);
lean_dec(v_a_2033_);
lean_del_object(v___x_2024_);
lean_dec(v_snd_2022_);
lean_dec(v_fst_2021_);
lean_dec(v_origAllocId_2012_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
v_a_2118_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2046_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2046_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
else
{
lean_dec(v_a_2033_);
lean_del_object(v___x_2024_);
lean_dec(v_snd_2022_);
lean_dec(v_fst_2021_);
lean_dec(v_origAllocId_2012_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
return v___x_2040_;
}
}
else
{
lean_dec(v_a_2033_);
lean_del_object(v___x_2024_);
lean_dec(v_snd_2022_);
lean_dec(v_fst_2021_);
lean_dec(v_origAllocId_2012_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
return v___x_2037_;
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_del_object(v___x_2024_);
lean_dec(v_snd_2022_);
lean_dec(v_fst_2021_);
lean_dec_ref(v_k_2013_);
lean_dec(v_origAllocId_2012_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
v_a_2127_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2032_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2032_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_2024_);
lean_dec(v_snd_2022_);
lean_dec(v_fst_2021_);
lean_dec_ref(v_k_2013_);
lean_dec(v_origAllocId_2012_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
v_a_2135_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2027_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2027_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v_k_2013_);
lean_dec(v_origAllocId_2012_);
lean_dec_ref(v_decl_2010_);
lean_dec_ref(v_currentRetType_2008_);
v_a_2144_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2019_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2019_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object* v_resultType_2152_, lean_object* v_x_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(v_resultType_2152_, v_x_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object* v_resultType_2160_, lean_object* v_i_2161_, lean_object* v_as_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = lean_array_get_size(v_as_2162_);
v___x_2169_ = lean_nat_dec_lt(v_i_2161_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; 
lean_dec(v_i_2161_);
lean_dec_ref(v_resultType_2160_);
v___x_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2170_, 0, v_as_2162_);
return v___x_2170_;
}
else
{
lean_object* v___f_2171_; lean_object* v_a_2172_; lean_object* v___x_2173_; 
lean_inc_ref(v_resultType_2160_);
v___f_2171_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2171_, 0, v_resultType_2160_);
v_a_2172_ = lean_array_fget_borrowed(v_as_2162_, v_i_2161_);
lean_inc(v_a_2172_);
v___x_2173_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_2172_, v___f_2171_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; size_t v___x_2175_; size_t v___x_2176_; uint8_t v___x_2177_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref(v___x_2173_);
v___x_2175_ = lean_ptr_addr(v_a_2172_);
v___x_2176_ = lean_ptr_addr(v_a_2174_);
v___x_2177_ = lean_usize_dec_eq(v___x_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_add(v_i_2161_, v___x_2178_);
v___x_2180_ = lean_array_fset(v_as_2162_, v_i_2161_, v_a_2174_);
lean_dec(v_i_2161_);
v_i_2161_ = v___x_2179_;
v_as_2162_ = v___x_2180_;
goto _start;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec(v_a_2174_);
v___x_2182_ = lean_unsigned_to_nat(1u);
v___x_2183_ = lean_nat_add(v_i_2161_, v___x_2182_);
lean_dec(v_i_2161_);
v_i_2161_ = v___x_2183_;
goto _start;
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v_as_2162_);
lean_dec(v_i_2161_);
lean_dec_ref(v_resultType_2160_);
v_a_2185_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2173_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2173_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object* v_code_2193_, lean_object* v_ds_2194_, lean_object* v_currentRetType_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_code_2202_; lean_object* v_ds_2203_; lean_object* v_k_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; 
switch(lean_obj_tag(v_code_2193_))
{
case 0:
{
lean_object* v_decl_2213_; lean_object* v_value_2214_; 
v_decl_2213_ = lean_ctor_get(v_code_2193_, 0);
v_value_2214_ = lean_ctor_get(v_decl_2213_, 3);
if (lean_obj_tag(v_value_2214_) == 11)
{
lean_object* v_k_2215_; lean_object* v_n_2216_; lean_object* v_var_2217_; lean_object* v___x_2218_; 
lean_inc_ref(v_decl_2213_);
v_k_2215_ = lean_ctor_get(v_code_2193_, 1);
lean_inc_ref(v_k_2215_);
lean_dec_ref(v_code_2193_);
v_n_2216_ = lean_ctor_get(v_value_2214_, 0);
lean_inc(v_n_2216_);
v_var_2217_ = lean_ctor_get(v_value_2214_, 1);
lean_inc(v_var_2217_);
v___x_2218_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2195_, v_ds_2194_, v_decl_2213_, v_n_2216_, v_var_2217_, v_k_2215_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
return v___x_2218_;
}
else
{
lean_object* v_k_2219_; 
v_k_2219_ = lean_ctor_get(v_code_2193_, 1);
lean_inc_ref(v_k_2219_);
v_code_2202_ = v_code_2193_;
v_ds_2203_ = v_ds_2194_;
v_k_2204_ = v_k_2219_;
v___y_2205_ = v_a_2196_;
v___y_2206_ = v_a_2197_;
v___y_2207_ = v_a_2198_;
v___y_2208_ = v_a_2199_;
goto v___jp_2201_;
}
}
case 2:
{
lean_object* v_decl_2220_; lean_object* v_k_2221_; lean_object* v_params_2222_; lean_object* v_type_2223_; lean_object* v_value_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_decl_2220_ = lean_ctor_get(v_code_2193_, 0);
lean_inc_ref(v_decl_2220_);
v_k_2221_ = lean_ctor_get(v_code_2193_, 1);
lean_inc_ref(v_k_2221_);
lean_dec_ref(v_code_2193_);
v_params_2222_ = lean_ctor_get(v_decl_2220_, 2);
lean_inc_ref(v_params_2222_);
v_type_2223_ = lean_ctor_get(v_decl_2220_, 3);
lean_inc_ref_n(v_type_2223_, 2);
v_value_2224_ = lean_ctor_get(v_decl_2220_, 4);
v___x_2225_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_value_2224_);
v___x_2226_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_value_2224_, v___x_2225_, v_type_2223_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2247_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2247_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2247_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
uint8_t v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = 1;
v___x_2232_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2231_, v_decl_2220_, v_type_2223_, v_params_2222_, v_a_2227_, v_a_2197_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref(v___x_2232_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set_tag(v___x_2229_, 2);
lean_ctor_set(v___x_2229_, 0, v_a_2233_);
v___x_2235_ = v___x_2229_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2233_);
v___x_2235_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_array_push(v_ds_2194_, v___x_2235_);
v_code_2193_ = v_k_2221_;
v_ds_2194_ = v___x_2236_;
goto _start;
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_del_object(v___x_2229_);
lean_dec_ref(v_k_2221_);
lean_dec_ref(v_currentRetType_2195_);
lean_dec_ref(v_ds_2194_);
v_a_2239_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2232_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2232_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_2223_);
lean_dec_ref(v_params_2222_);
lean_dec_ref(v_k_2221_);
lean_dec_ref(v_decl_2220_);
lean_dec_ref(v_currentRetType_2195_);
lean_dec_ref(v_ds_2194_);
return v___x_2226_;
}
}
case 4:
{
lean_object* v_cases_2248_; lean_object* v_typeName_2249_; lean_object* v_resultType_2250_; lean_object* v_discr_2251_; lean_object* v_alts_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref(v_currentRetType_2195_);
v_cases_2248_ = lean_ctor_get(v_code_2193_, 0);
lean_inc_ref(v_cases_2248_);
v_typeName_2249_ = lean_ctor_get(v_cases_2248_, 0);
v_resultType_2250_ = lean_ctor_get(v_cases_2248_, 1);
v_discr_2251_ = lean_ctor_get(v_cases_2248_, 2);
v_alts_2252_ = lean_ctor_get(v_cases_2248_, 3);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_cases_2248_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2254_ = v_cases_2248_;
v_isShared_2255_ = v_isSharedCheck_2292_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_alts_2252_);
lean_inc(v_discr_2251_);
lean_inc(v_resultType_2250_);
lean_inc(v_typeName_2249_);
lean_dec(v_cases_2248_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2292_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2252_);
lean_inc_ref(v_resultType_2250_);
v___x_2257_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2250_, v___x_2256_, v_alts_2252_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2283_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2283_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2283_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
uint8_t v___x_2262_; lean_object* v___y_2264_; size_t v___x_2269_; size_t v___x_2270_; uint8_t v___x_2271_; 
v___x_2262_ = 1;
v___x_2269_ = lean_ptr_addr(v_alts_2252_);
lean_dec_ref(v_alts_2252_);
v___x_2270_ = lean_ptr_addr(v_a_2258_);
v___x_2271_ = lean_usize_dec_eq(v___x_2269_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2281_; 
v_isSharedCheck_2281_ = !lean_is_exclusive(v_code_2193_);
if (v_isSharedCheck_2281_ == 0)
{
lean_object* v_unused_2282_; 
v_unused_2282_ = lean_ctor_get(v_code_2193_, 0);
lean_dec(v_unused_2282_);
v___x_2273_ = v_code_2193_;
v_isShared_2274_ = v_isSharedCheck_2281_;
goto v_resetjp_2272_;
}
else
{
lean_dec(v_code_2193_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2281_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 3, v_a_2258_);
v___x_2276_ = v___x_2254_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_typeName_2249_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_resultType_2250_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_discr_2251_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v_a_2258_);
v___x_2276_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2276_);
v___x_2278_ = v___x_2273_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
v___y_2264_ = v___x_2278_;
goto v___jp_2263_;
}
}
}
}
else
{
lean_dec(v_a_2258_);
lean_del_object(v___x_2254_);
lean_dec(v_discr_2251_);
lean_dec_ref(v_resultType_2250_);
lean_dec(v_typeName_2249_);
v___y_2264_ = v_code_2193_;
goto v___jp_2263_;
}
v___jp_2263_:
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2265_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2262_, v_ds_2194_, v___y_2264_);
lean_dec_ref(v_ds_2194_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2265_);
v___x_2267_ = v___x_2260_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_del_object(v___x_2254_);
lean_dec_ref(v_alts_2252_);
lean_dec(v_discr_2251_);
lean_dec_ref(v_resultType_2250_);
lean_dec(v_typeName_2249_);
lean_dec_ref(v_code_2193_);
lean_dec_ref(v_ds_2194_);
v_a_2284_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2257_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2257_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
case 7:
{
lean_object* v_k_2293_; 
v_k_2293_ = lean_ctor_get(v_code_2193_, 3);
lean_inc_ref(v_k_2293_);
v_code_2202_ = v_code_2193_;
v_ds_2203_ = v_ds_2194_;
v_k_2204_ = v_k_2293_;
v___y_2205_ = v_a_2196_;
v___y_2206_ = v_a_2197_;
v___y_2207_ = v_a_2198_;
v___y_2208_ = v_a_2199_;
goto v___jp_2201_;
}
case 8:
{
lean_object* v_k_2294_; 
v_k_2294_ = lean_ctor_get(v_code_2193_, 3);
lean_inc_ref(v_k_2294_);
v_code_2202_ = v_code_2193_;
v_ds_2203_ = v_ds_2194_;
v_k_2204_ = v_k_2294_;
v___y_2205_ = v_a_2196_;
v___y_2206_ = v_a_2197_;
v___y_2207_ = v_a_2198_;
v___y_2208_ = v_a_2199_;
goto v___jp_2201_;
}
case 9:
{
lean_object* v_k_2295_; 
v_k_2295_ = lean_ctor_get(v_code_2193_, 5);
lean_inc_ref(v_k_2295_);
v_code_2202_ = v_code_2193_;
v_ds_2203_ = v_ds_2194_;
v_k_2204_ = v_k_2295_;
v___y_2205_ = v_a_2196_;
v___y_2206_ = v_a_2197_;
v___y_2207_ = v_a_2198_;
v___y_2208_ = v_a_2199_;
goto v___jp_2201_;
}
case 10:
{
lean_object* v_k_2296_; 
v_k_2296_ = lean_ctor_get(v_code_2193_, 2);
lean_inc_ref(v_k_2296_);
v_code_2202_ = v_code_2193_;
v_ds_2203_ = v_ds_2194_;
v_k_2204_ = v_k_2296_;
v___y_2205_ = v_a_2196_;
v___y_2206_ = v_a_2197_;
v___y_2207_ = v_a_2198_;
v___y_2208_ = v_a_2199_;
goto v___jp_2201_;
}
case 11:
{
lean_object* v_k_2297_; 
v_k_2297_ = lean_ctor_get(v_code_2193_, 2);
lean_inc_ref(v_k_2297_);
v_code_2202_ = v_code_2193_;
v_ds_2203_ = v_ds_2194_;
v_k_2204_ = v_k_2297_;
v___y_2205_ = v_a_2196_;
v___y_2206_ = v_a_2197_;
v___y_2207_ = v_a_2198_;
v___y_2208_ = v_a_2199_;
goto v___jp_2201_;
}
case 12:
{
lean_object* v_k_2298_; 
v_k_2298_ = lean_ctor_get(v_code_2193_, 2);
lean_inc_ref(v_k_2298_);
v_code_2202_ = v_code_2193_;
v_ds_2203_ = v_ds_2194_;
v_k_2204_ = v_k_2298_;
v___y_2205_ = v_a_2196_;
v___y_2206_ = v_a_2197_;
v___y_2207_ = v_a_2198_;
v___y_2208_ = v_a_2199_;
goto v___jp_2201_;
}
case 13:
{
lean_object* v_k_2299_; 
v_k_2299_ = lean_ctor_get(v_code_2193_, 1);
lean_inc_ref(v_k_2299_);
v_code_2202_ = v_code_2193_;
v_ds_2203_ = v_ds_2194_;
v_k_2204_ = v_k_2299_;
v___y_2205_ = v_a_2196_;
v___y_2206_ = v_a_2197_;
v___y_2207_ = v_a_2198_;
v___y_2208_ = v_a_2199_;
goto v___jp_2201_;
}
default: 
{
uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec_ref(v_currentRetType_2195_);
v___x_2300_ = 1;
v___x_2301_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2300_, v_ds_2194_, v_code_2193_);
lean_dec_ref(v_ds_2194_);
v___x_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
return v___x_2302_;
}
}
v___jp_2201_:
{
uint8_t v___x_2209_; lean_object* v_d_2210_; lean_object* v___x_2211_; 
v___x_2209_ = 1;
v_d_2210_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_2209_, v_code_2202_);
lean_dec_ref(v_code_2202_);
v___x_2211_ = lean_array_push(v_ds_2203_, v_d_2210_);
v_code_2193_ = v_k_2204_;
v_ds_2194_ = v___x_2211_;
v_a_2196_ = v___y_2205_;
v_a_2197_ = v___y_2206_;
v_a_2198_ = v___y_2207_;
v_a_2199_ = v___y_2208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object* v_resultType_2303_, lean_object* v_x_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2311_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2304_, v___x_2310_, v_resultType_2303_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object* v_resultType_2312_, lean_object* v_i_2313_, lean_object* v_as_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2312_, v_i_2313_, v_as_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object* v_code_2321_, lean_object* v_ds_2322_, lean_object* v_currentRetType_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_code_2321_, v_ds_2322_, v_currentRetType_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object* v_currentRetType_2330_, lean_object* v_ds_2331_, lean_object* v_decl_2332_, lean_object* v_nFields_2333_, lean_object* v_origAllocId_2334_, lean_object* v_k_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2330_, v_ds_2331_, v_decl_2332_, v_nFields_2333_, v_origAllocId_2334_, v_k_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object* v_f_2342_, lean_object* v_v_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
if (lean_obj_tag(v_v_2343_) == 0)
{
lean_object* v_code_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2373_; 
v_code_2349_ = lean_ctor_get(v_v_2343_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_v_2343_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2351_ = v_v_2343_;
v_isShared_2352_ = v_isSharedCheck_2373_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_code_2349_);
lean_dec(v_v_2343_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2373_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; 
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
v___x_2353_ = lean_apply_6(v_f_2342_, v_code_2349_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, lean_box(0));
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2364_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2364_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2364_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v_a_2354_);
v___x_2359_ = v___x_2351_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2361_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2359_);
v___x_2361_ = v___x_2356_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_del_object(v___x_2351_);
v_a_2365_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2353_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2353_);
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
lean_object* v___x_2374_; 
lean_dec_ref(v_f_2342_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v_v_2343_);
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object* v_f_2375_, lean_object* v_v_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2375_, v_v_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t v_pu_2383_, lean_object* v_f_2384_, lean_object* v_v_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2384_, v_v_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object* v_pu_2392_, lean_object* v_f_2393_, lean_object* v_v_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
uint8_t v_pu_boxed_2400_; lean_object* v_res_2401_; 
v_pu_boxed_2400_ = lean_unbox(v_pu_2392_);
v_res_2401_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(v_pu_boxed_2400_, v_f_2393_, v_v_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object* v_toSignature_2402_, lean_object* v_x_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_type_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_type_2409_ = lean_ctor_get(v_toSignature_2402_, 2);
lean_inc_ref(v_type_2409_);
lean_dec_ref(v_toSignature_2402_);
v___x_2410_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2411_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2403_, v___x_2410_, v_type_2409_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object* v_toSignature_2412_, lean_object* v_x_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(v_toSignature_2412_, v_x_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object* v_decl_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2421_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2464_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2464_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2464_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
uint8_t v_resetReuse_2431_; 
v_resetReuse_2431_ = lean_ctor_get_uint8(v_a_2427_, sizeof(void*)*4 + 2);
lean_dec(v_a_2427_);
if (v_resetReuse_2431_ == 0)
{
lean_object* v___x_2433_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v_decl_2420_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_decl_2420_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
else
{
lean_object* v_toSignature_2435_; lean_object* v_value_2436_; uint8_t v_recursive_2437_; lean_object* v_inlineAttr_x3f_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2463_; 
lean_del_object(v___x_2429_);
v_toSignature_2435_ = lean_ctor_get(v_decl_2420_, 0);
v_value_2436_ = lean_ctor_get(v_decl_2420_, 1);
v_recursive_2437_ = lean_ctor_get_uint8(v_decl_2420_, sizeof(void*)*3);
v_inlineAttr_x3f_2438_ = lean_ctor_get(v_decl_2420_, 2);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2440_ = v_decl_2420_;
v_isShared_2441_ = v_isSharedCheck_2463_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_inlineAttr_x3f_2438_);
lean_inc(v_value_2436_);
lean_inc(v_toSignature_2435_);
lean_dec(v_decl_2420_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2463_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___f_2442_; lean_object* v___x_2443_; 
lean_inc_ref(v_toSignature_2435_);
v___f_2442_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2442_, 0, v_toSignature_2435_);
v___x_2443_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v___f_2442_, v_value_2436_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2454_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2454_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2454_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 1, v_a_2444_);
v___x_2449_ = v___x_2440_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_toSignature_2435_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_a_2444_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v_inlineAttr_x3f_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2453_, sizeof(void*)*3, v_recursive_2437_);
v___x_2449_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2451_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2449_);
v___x_2451_ = v___x_2446_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_del_object(v___x_2440_);
lean_dec(v_inlineAttr_x3f_2438_);
lean_dec_ref(v_toSignature_2435_);
v_a_2455_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2443_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2443_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v_decl_2420_);
v_a_2465_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2426_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2426_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object* v_decl_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(v_decl_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
return v_res_2479_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__2));
v___x_2486_ = 2;
v___x_2487_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__1));
v___x_2488_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_2487_, v___x_2486_, v___x_2485_, v___x_2484_);
return v___x_2488_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse(void){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_obj_once(&l_Lean_Compiler_LCNF_expandResetReuse___closed__3, &l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3);
return v___x_2489_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_unsigned_to_nat(2743268278u);
v___x_2546_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2547_ = l_Lean_Name_num___override(v___x_2546_, v___x_2545_);
return v___x_2547_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2550_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2551_ = l_Lean_Name_str___override(v___x_2550_, v___x_2549_);
return v___x_2551_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2554_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2555_ = l_Lean_Name_str___override(v___x_2554_, v___x_2553_);
return v___x_2555_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = lean_unsigned_to_nat(2u);
v___x_2557_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2558_ = l_Lean_Name_num___override(v___x_2557_, v___x_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2560_; uint8_t v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2560_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2561_ = 1;
v___x_2562_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2563_ = l_Lean_registerTraceClass(v___x_2560_, v___x_2561_, v___x_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
return v_res_2565_;
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
