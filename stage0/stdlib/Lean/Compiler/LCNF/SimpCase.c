// Lean compiler output
// Module: Lean.Compiler.LCNF.SimpCase
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.AlphaEqv import Init.Omega
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.SimpCase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Compiler.LCNF.SimpCase.0.Lean.Compiler.LCNF.addDefaultAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureHasDefault(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_simpCase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpCase"};
static const lean_object* l_Lean_Compiler_LCNF_simpCase___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_simpCase___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_simpCase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_simpCase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 92, 41, 80, 34, 13, 30, 2)}};
static const lean_object* l_Lean_Compiler_LCNF_simpCase___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_simpCase___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_simpCase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_simpCase___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_simpCase___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_simpCase___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_simpCase___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simpCase;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_simpCase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 115, 95, 67, 81, 150, 198, 169)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "SimpCase"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 85, 95, 162, 237, 93, 136, 210)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(149, 85, 1, 1, 249, 114, 201, 242)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(128, 195, 27, 71, 70, 238, 5, 249)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(218, 73, 79, 143, 6, 98, 132, 204)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 66, 31, 97, 69, 225, 237, 3)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 203, 5, 135, 216, 0, 147, 100)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 166, 14, 190, 157, 30, 192, 24)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 200, 250, 209, 136, 24, 111, 216)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 208, 198, 202, 11, 103, 204, 69)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 185, 0, 153, 59, 162, 228, 227)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 14, 40, 21, 139, 206, 91, 108)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1808010913) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(44, 138, 246, 18, 227, 5, 112, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 122, 251, 129, 187, 139, 157, 59)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 16, 117, 131, 59, 32, 143, 15)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(70, 179, 246, 216, 56, 171, 143, 161)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(lean_object* v_upperBound_1_, lean_object* v_alts_2_, lean_object* v_code_3_, lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_lt(v_a_4_, v_upperBound_1_);
if (v___x_6_ == 0)
{
lean_dec(v_a_4_);
lean_dec_ref(v_code_3_);
return v_b_5_;
}
else
{
uint8_t v___x_7_; lean_object* v_n_8_; lean_object* v_a_10_; lean_object* v___y_14_; lean_object* v___x_17_; 
v___x_7_ = 1;
v_n_8_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_array_fget_borrowed(v_alts_2_, v_a_4_);
switch(lean_obj_tag(v___x_17_))
{
case 0:
{
lean_object* v_code_18_; 
v_code_18_ = lean_ctor_get(v___x_17_, 2);
lean_inc_ref(v_code_18_);
v___y_14_ = v_code_18_;
goto v___jp_13_;
}
case 1:
{
lean_object* v_code_19_; 
v_code_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc_ref(v_code_19_);
v___y_14_ = v_code_19_;
goto v___jp_13_;
}
default: 
{
lean_object* v_code_20_; 
v_code_20_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_code_20_);
v___y_14_ = v_code_20_;
goto v___jp_13_;
}
}
v___jp_9_:
{
lean_object* v___x_11_; 
v___x_11_ = lean_nat_add(v_a_4_, v_n_8_);
lean_dec(v_a_4_);
v_a_4_ = v___x_11_;
v_b_5_ = v_a_10_;
goto _start;
}
v___jp_13_:
{
uint8_t v___x_15_; 
lean_inc_ref(v_code_3_);
v___x_15_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_7_, v___y_14_, v_code_3_);
if (v___x_15_ == 0)
{
v_a_10_ = v_b_5_;
goto v___jp_9_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = lean_nat_add(v_b_5_, v_n_8_);
lean_dec(v_b_5_);
v_a_10_ = v___x_16_;
goto v___jp_9_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg___boxed(lean_object* v_upperBound_21_, lean_object* v_alts_22_, lean_object* v_code_23_, lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_21_, v_alts_22_, v_code_23_, v_a_24_, v_b_25_);
lean_dec_ref(v_alts_22_);
lean_dec(v_upperBound_21_);
return v_res_26_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0(void){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(lean_object* v_alts_28_, lean_object* v_i_29_){
_start:
{
lean_object* v___x_30_; lean_object* v_n_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_30_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0, &l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
v_n_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_nat_add(v_i_29_, v_n_31_);
v___x_33_ = lean_array_get_size(v_alts_28_);
v___x_34_ = lean_array_get_borrowed(v___x_30_, v_alts_28_, v_i_29_);
switch(lean_obj_tag(v___x_34_))
{
case 0:
{
lean_object* v_code_35_; lean_object* v___x_36_; 
v_code_35_ = lean_ctor_get(v___x_34_, 2);
lean_inc_ref(v_code_35_);
v___x_36_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_33_, v_alts_28_, v_code_35_, v___x_32_, v_n_31_);
return v___x_36_;
}
case 1:
{
lean_object* v_code_37_; lean_object* v___x_38_; 
v_code_37_ = lean_ctor_get(v___x_34_, 1);
lean_inc_ref(v_code_37_);
v___x_38_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_33_, v_alts_28_, v_code_37_, v___x_32_, v_n_31_);
return v___x_38_;
}
default: 
{
lean_object* v_code_39_; lean_object* v___x_40_; 
v_code_39_ = lean_ctor_get(v___x_34_, 0);
lean_inc_ref(v_code_39_);
v___x_40_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_33_, v_alts_28_, v_code_39_, v___x_32_, v_n_31_);
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___boxed(lean_object* v_alts_41_, lean_object* v_i_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(v_alts_41_, v_i_42_);
lean_dec(v_i_42_);
lean_dec_ref(v_alts_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0(lean_object* v_upperBound_44_, lean_object* v_alts_45_, lean_object* v_code_46_, lean_object* v_inst_47_, lean_object* v_R_48_, lean_object* v_a_49_, lean_object* v_b_50_, lean_object* v_c_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_44_, v_alts_45_, v_code_46_, v_a_49_, v_b_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___boxed(lean_object* v_upperBound_53_, lean_object* v_alts_54_, lean_object* v_code_55_, lean_object* v_inst_56_, lean_object* v_R_57_, lean_object* v_a_58_, lean_object* v_b_59_, lean_object* v_c_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0(v_upperBound_53_, v_alts_54_, v_code_55_, v_inst_56_, v_R_57_, v_a_58_, v_b_59_, v_c_60_);
lean_dec_ref(v_alts_54_);
lean_dec(v_upperBound_53_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(lean_object* v_upperBound_62_, lean_object* v_alts_63_, lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
lean_object* v_a_67_; uint8_t v___x_71_; 
v___x_71_ = lean_nat_dec_lt(v_a_64_, v_upperBound_62_);
if (v___x_71_ == 0)
{
lean_dec(v_a_64_);
return v_b_65_;
}
else
{
lean_object* v_fst_72_; lean_object* v_snd_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_86_; 
v_fst_72_ = lean_ctor_get(v_b_65_, 0);
v_snd_73_ = lean_ctor_get(v_b_65_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_b_65_);
if (v_isSharedCheck_86_ == 0)
{
v___x_75_ = v_b_65_;
v_isShared_76_ = v_isSharedCheck_86_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_snd_73_);
lean_inc(v_fst_72_);
lean_dec(v_b_65_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_86_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(v_alts_63_, v_a_64_);
v___x_78_ = lean_nat_dec_lt(v_snd_73_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_80_; 
lean_dec(v___x_77_);
if (v_isShared_76_ == 0)
{
v___x_80_ = v___x_75_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_fst_72_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_snd_73_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
v_a_67_ = v___x_80_;
goto v___jp_66_;
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_84_; 
lean_dec(v_snd_73_);
lean_dec(v_fst_72_);
v___x_82_ = lean_array_fget_borrowed(v_alts_63_, v_a_64_);
lean_inc(v___x_82_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_77_);
lean_ctor_set(v___x_75_, 0, v___x_82_);
v___x_84_ = v___x_75_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_77_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
v_a_67_ = v___x_84_;
goto v___jp_66_;
}
}
}
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_add(v_a_64_, v___x_68_);
lean_dec(v_a_64_);
v_a_64_ = v___x_69_;
v_b_65_ = v_a_67_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg___boxed(lean_object* v_upperBound_87_, lean_object* v_alts_88_, lean_object* v_a_89_, lean_object* v_b_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v_upperBound_87_, v_alts_88_, v_a_89_, v_b_90_);
lean_dec_ref(v_alts_88_);
lean_dec(v_upperBound_87_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(lean_object* v_alts_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v_maxAlt_97_; lean_object* v_max_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v_fst_101_; lean_object* v_snd_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v___x_93_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0, &l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_array_get_size(v_alts_92_);
v___x_96_ = lean_unsigned_to_nat(0u);
v_maxAlt_97_ = lean_array_get_borrowed(v___x_93_, v_alts_92_, v___x_96_);
v_max_98_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(v_alts_92_, v___x_96_);
lean_inc(v_maxAlt_97_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v_maxAlt_97_);
lean_ctor_set(v___x_99_, 1, v_max_98_);
v___x_100_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v___x_95_, v_alts_92_, v___x_94_, v___x_99_);
v_fst_101_ = lean_ctor_get(v___x_100_, 0);
v_snd_102_ = lean_ctor_get(v___x_100_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_100_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_snd_102_);
lean_inc(v_fst_101_);
lean_dec(v___x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_fst_101_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_snd_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs___boxed(lean_object* v_alts_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(v_alts_110_);
lean_dec_ref(v_alts_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0(lean_object* v_upperBound_112_, lean_object* v_alts_113_, lean_object* v_inst_114_, lean_object* v_R_115_, lean_object* v_a_116_, lean_object* v_b_117_, lean_object* v_c_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v_upperBound_112_, v_alts_113_, v_a_116_, v_b_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___boxed(lean_object* v_upperBound_120_, lean_object* v_alts_121_, lean_object* v_inst_122_, lean_object* v_R_123_, lean_object* v_a_124_, lean_object* v_b_125_, lean_object* v_c_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0(v_upperBound_120_, v_alts_121_, v_inst_122_, v_R_123_, v_a_124_, v_b_125_, v_c_126_);
lean_dec_ref(v_alts_121_);
lean_dec(v_upperBound_120_);
return v_res_127_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_instMonadEIO___redArg();
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_toApplicative_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_172_; 
v___x_137_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0);
v___x_138_ = l_StateRefT_x27_instMonad___redArg(v___x_137_);
v_toApplicative_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; 
v_unused_173_ = lean_ctor_get(v___x_138_, 1);
lean_dec(v_unused_173_);
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_172_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_toApplicative_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_172_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_toFunctor_143_; lean_object* v_toSeq_144_; lean_object* v_toSeqLeft_145_; lean_object* v_toSeqRight_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_170_; 
v_toFunctor_143_ = lean_ctor_get(v_toApplicative_139_, 0);
v_toSeq_144_ = lean_ctor_get(v_toApplicative_139_, 2);
v_toSeqLeft_145_ = lean_ctor_get(v_toApplicative_139_, 3);
v_toSeqRight_146_ = lean_ctor_get(v_toApplicative_139_, 4);
v_isSharedCheck_170_ = !lean_is_exclusive(v_toApplicative_139_);
if (v_isSharedCheck_170_ == 0)
{
lean_object* v_unused_171_; 
v_unused_171_ = lean_ctor_get(v_toApplicative_139_, 1);
lean_dec(v_unused_171_);
v___x_148_ = v_toApplicative_139_;
v_isShared_149_ = v_isSharedCheck_170_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_toSeqRight_146_);
lean_inc(v_toSeqLeft_145_);
lean_inc(v_toSeq_144_);
lean_inc(v_toFunctor_143_);
lean_dec(v_toApplicative_139_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_170_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___f_150_; lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___x_159_; 
v___f_150_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1));
v___f_151_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2));
lean_inc_ref(v_toFunctor_143_);
v___f_152_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_152_, 0, v_toFunctor_143_);
v___f_153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_153_, 0, v_toFunctor_143_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___f_152_);
lean_ctor_set(v___x_154_, 1, v___f_153_);
v___f_155_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_155_, 0, v_toSeqRight_146_);
v___f_156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_156_, 0, v_toSeqLeft_145_);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_157_, 0, v_toSeq_144_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 4, v___f_155_);
lean_ctor_set(v___x_148_, 3, v___f_156_);
lean_ctor_set(v___x_148_, 2, v___f_157_);
lean_ctor_set(v___x_148_, 1, v___f_150_);
lean_ctor_set(v___x_148_, 0, v___x_154_);
v___x_159_ = v___x_148_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___f_150_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v___f_157_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v___f_156_);
lean_ctor_set(v_reuseFailAlloc_169_, 4, v___f_155_);
v___x_159_ = v_reuseFailAlloc_169_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_161_; 
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v___f_151_);
lean_ctor_set(v___x_141_, 0, v___x_159_);
v___x_161_ = v___x_141_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___f_151_);
v___x_161_ = v_reuseFailAlloc_168_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___x_1678__overap_166_; lean_object* v___x_167_; 
v___x_162_ = l_StateRefT_x27_instMonad___redArg(v___x_161_);
v___x_163_ = lean_box(0);
v___x_164_ = l_instInhabitedOfMonad___redArg(v___x_162_, v___x_163_);
v___f_165_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_165_, 0, v___x_164_);
v___x_1678__overap_166_ = lean_panic_fn_borrowed(v___f_165_, v_msg_131_);
lean_dec_ref(v___f_165_);
lean_inc(v___y_135_);
lean_inc_ref(v___y_134_);
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
v___x_167_ = lean_apply_5(v___x_1678__overap_166_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, lean_box(0));
return v___x_167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___boxed(lean_object* v_msg_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v_msg_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_180_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2));
v___x_185_ = lean_unsigned_to_nat(36u);
v___x_186_ = lean_unsigned_to_nat(77u);
v___x_187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1));
v___x_188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0));
v___x_189_ = l_mkPanicMessageWithDecl(v___x_188_, v___x_187_, v___x_186_, v___x_185_, v___x_184_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(lean_object* v_snd_190_, lean_object* v_fst_191_, lean_object* v_as_192_, size_t v_sz_193_, size_t v_i_194_, lean_object* v_b_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_a_202_; uint8_t v___x_206_; 
v___x_206_ = lean_usize_dec_lt(v_i_194_, v_sz_193_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
lean_dec_ref(v_fst_191_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v_b_195_);
return v___x_207_;
}
else
{
lean_object* v_fst_208_; lean_object* v_snd_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_258_; 
v_fst_208_ = lean_ctor_get(v_b_195_, 0);
v_snd_209_ = lean_ctor_get(v_b_195_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_b_195_);
if (v_isSharedCheck_258_ == 0)
{
v___x_211_ = v_b_195_;
v_isShared_212_ = v_isSharedCheck_258_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_snd_209_);
lean_inc(v_fst_208_);
lean_dec(v_b_195_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_258_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; uint8_t v_first_214_; lean_object* v_a_220_; uint8_t v___x_221_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_251_; 
v___x_213_ = lean_unsigned_to_nat(1u);
v_first_214_ = lean_nat_dec_eq(v_snd_190_, v___x_213_);
v_a_220_ = lean_array_uget_borrowed(v_as_192_, v_i_194_);
v___x_221_ = 1;
switch(lean_obj_tag(v_a_220_))
{
case 0:
{
lean_object* v_code_255_; 
v_code_255_ = lean_ctor_get(v_a_220_, 2);
lean_inc_ref(v_code_255_);
v___y_251_ = v_code_255_;
goto v___jp_250_;
}
case 1:
{
lean_object* v_code_256_; 
v_code_256_ = lean_ctor_get(v_a_220_, 1);
lean_inc_ref(v_code_256_);
v___y_251_ = v_code_256_;
goto v___jp_250_;
}
default: 
{
lean_object* v_code_257_; 
v_code_257_ = lean_ctor_get(v_a_220_, 0);
lean_inc_ref(v_code_257_);
v___y_251_ = v_code_257_;
goto v___jp_250_;
}
}
v___jp_215_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_box(v_first_214_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v___x_216_);
v___x_218_ = v___x_211_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_fst_208_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
v_a_202_ = v___x_218_;
goto v___jp_201_;
}
}
v___jp_222_:
{
uint8_t v___x_225_; 
v___x_225_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_221_, v___y_223_, v___y_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_del_object(v___x_211_);
lean_inc(v_a_220_);
v___x_226_ = lean_array_push(v_fst_208_, v_a_220_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_snd_209_);
v_a_202_ = v___x_227_;
goto v___jp_201_;
}
else
{
if (lean_obj_tag(v_a_220_) == 1)
{
uint8_t v___x_228_; 
v___x_228_ = lean_unbox(v_snd_209_);
lean_dec(v_snd_209_);
if (v___x_228_ == 0)
{
lean_object* v_code_229_; lean_object* v___x_230_; 
v_code_229_ = lean_ctor_get(v_a_220_, 1);
v___x_230_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_221_, v_code_229_, v___y_197_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_dec_ref_known(v___x_230_, 1);
goto v___jp_215_;
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_del_object(v___x_211_);
lean_dec(v_fst_208_);
lean_dec_ref(v_fst_191_);
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
goto v___jp_215_;
}
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_del_object(v___x_211_);
v___x_239_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3);
v___x_240_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v___x_239_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; 
lean_dec_ref_known(v___x_240_, 1);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_fst_208_);
lean_ctor_set(v___x_241_, 1, v_snd_209_);
v_a_202_ = v___x_241_;
goto v___jp_201_;
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec(v_snd_209_);
lean_dec(v_fst_208_);
lean_dec_ref(v_fst_191_);
v_a_242_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_240_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
}
v___jp_250_:
{
switch(lean_obj_tag(v_fst_191_))
{
case 0:
{
lean_object* v_code_252_; 
v_code_252_ = lean_ctor_get(v_fst_191_, 2);
lean_inc_ref(v_code_252_);
v___y_223_ = v___y_251_;
v___y_224_ = v_code_252_;
goto v___jp_222_;
}
case 1:
{
lean_object* v_code_253_; 
v_code_253_ = lean_ctor_get(v_fst_191_, 1);
lean_inc_ref(v_code_253_);
v___y_223_ = v___y_251_;
v___y_224_ = v_code_253_;
goto v___jp_222_;
}
default: 
{
lean_object* v_code_254_; 
v_code_254_ = lean_ctor_get(v_fst_191_, 0);
lean_inc_ref(v_code_254_);
v___y_223_ = v___y_251_;
v___y_224_ = v_code_254_;
goto v___jp_222_;
}
}
}
}
}
v___jp_201_:
{
size_t v___x_203_; size_t v___x_204_; 
v___x_203_ = ((size_t)1ULL);
v___x_204_ = lean_usize_add(v_i_194_, v___x_203_);
v_i_194_ = v___x_204_;
v_b_195_ = v_a_202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___boxed(lean_object* v_snd_259_, lean_object* v_fst_260_, lean_object* v_as_261_, lean_object* v_sz_262_, lean_object* v_i_263_, lean_object* v_b_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
size_t v_sz_boxed_270_; size_t v_i_boxed_271_; lean_object* v_res_272_; 
v_sz_boxed_270_ = lean_unbox_usize(v_sz_262_);
lean_dec(v_sz_262_);
v_i_boxed_271_ = lean_unbox_usize(v_i_263_);
lean_dec(v_i_263_);
v_res_272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_259_, v_fst_260_, v_as_261_, v_sz_boxed_270_, v_i_boxed_271_, v_b_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec_ref(v_as_261_);
lean_dec(v_snd_259_);
return v_res_272_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(lean_object* v___x_273_, lean_object* v_as_274_, size_t v_i_275_, size_t v_stop_276_){
_start:
{
uint8_t v___x_277_; 
v___x_277_ = lean_usize_dec_eq(v_i_275_, v_stop_276_);
if (v___x_277_ == 0)
{
uint8_t v___x_278_; lean_object* v___x_279_; 
v___x_278_ = 1;
v___x_279_ = lean_array_uget_borrowed(v_as_274_, v_i_275_);
if (lean_obj_tag(v___x_279_) == 2)
{
return v___x_278_;
}
else
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_dec_le(v___x_273_, v___x_280_);
if (v___x_281_ == 0)
{
size_t v___x_282_; size_t v___x_283_; 
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_add(v_i_275_, v___x_282_);
v_i_275_ = v___x_283_;
goto _start;
}
else
{
return v___x_278_;
}
}
}
else
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2___boxed(lean_object* v___x_286_, lean_object* v_as_287_, lean_object* v_i_288_, lean_object* v_stop_289_){
_start:
{
size_t v_i_boxed_290_; size_t v_stop_boxed_291_; uint8_t v_res_292_; lean_object* v_r_293_; 
v_i_boxed_290_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_stop_boxed_291_ = lean_unbox_usize(v_stop_289_);
lean_dec(v_stop_289_);
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(v___x_286_, v_as_287_, v_i_boxed_290_, v_stop_boxed_291_);
lean_dec_ref(v_as_287_);
lean_dec(v___x_286_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(lean_object* v_alts_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_339_; 
v___x_312_ = lean_array_get_size(v_alts_300_);
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_dec_le(v___x_312_, v___x_313_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_nat_dec_lt(v___x_340_, v___x_312_);
if (v___x_341_ == 0)
{
goto v___jp_314_;
}
else
{
if (v___x_341_ == 0)
{
goto v___jp_314_;
}
else
{
size_t v___x_342_; size_t v___x_343_; uint8_t v___x_344_; 
v___x_342_ = ((size_t)0ULL);
v___x_343_ = lean_usize_of_nat(v___x_312_);
v___x_344_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(v___x_312_, v_alts_300_, v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
goto v___jp_314_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v_alts_300_);
return v___x_345_;
}
}
}
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v_alts_300_);
return v___x_346_;
}
v___jp_306_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_309_, 0, v___y_308_);
v___x_310_ = lean_array_push(v___y_307_, v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
v___jp_314_:
{
lean_object* v___x_315_; lean_object* v_fst_316_; lean_object* v_snd_317_; uint8_t v_first_318_; 
v___x_315_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(v_alts_300_);
v_fst_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_fst_316_);
v_snd_317_ = lean_ctor_get(v___x_315_, 1);
lean_inc(v_snd_317_);
lean_dec_ref(v___x_315_);
v_first_318_ = lean_nat_dec_eq(v_snd_317_, v___x_313_);
if (v_first_318_ == 0)
{
lean_object* v___x_319_; size_t v_sz_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_319_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1));
v_sz_320_ = lean_array_size(v_alts_300_);
v___x_321_ = ((size_t)0ULL);
lean_inc(v_fst_316_);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_317_, v_fst_316_, v_alts_300_, v_sz_320_, v___x_321_, v___x_319_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
lean_dec_ref(v_alts_300_);
lean_dec(v_snd_317_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_322_, 1);
switch(lean_obj_tag(v_fst_316_))
{
case 0:
{
lean_object* v_fst_324_; lean_object* v_code_325_; 
v_fst_324_ = lean_ctor_get(v_a_323_, 0);
lean_inc(v_fst_324_);
lean_dec(v_a_323_);
v_code_325_ = lean_ctor_get(v_fst_316_, 2);
lean_inc_ref(v_code_325_);
lean_dec_ref_known(v_fst_316_, 3);
v___y_307_ = v_fst_324_;
v___y_308_ = v_code_325_;
goto v___jp_306_;
}
case 1:
{
lean_object* v_fst_326_; lean_object* v_code_327_; 
v_fst_326_ = lean_ctor_get(v_a_323_, 0);
lean_inc(v_fst_326_);
lean_dec(v_a_323_);
v_code_327_ = lean_ctor_get(v_fst_316_, 1);
lean_inc_ref(v_code_327_);
lean_dec_ref_known(v_fst_316_, 2);
v___y_307_ = v_fst_326_;
v___y_308_ = v_code_327_;
goto v___jp_306_;
}
default: 
{
lean_object* v_fst_328_; lean_object* v_code_329_; 
v_fst_328_ = lean_ctor_get(v_a_323_, 0);
lean_inc(v_fst_328_);
lean_dec(v_a_323_);
v_code_329_ = lean_ctor_get(v_fst_316_, 0);
lean_inc_ref(v_code_329_);
lean_dec_ref_known(v_fst_316_, 1);
v___y_307_ = v_fst_328_;
v___y_308_ = v_code_329_;
goto v___jp_306_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_fst_316_);
v_a_330_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_322_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_322_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v___x_338_; 
lean_dec(v_snd_317_);
lean_dec(v_fst_316_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_alts_300_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___boxed(lean_object* v_alts_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(v_alts_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(lean_object* v_as_354_, size_t v_i_355_, size_t v_stop_356_, lean_object* v_b_357_){
_start:
{
lean_object* v___y_359_; uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_eq(v_i_355_, v_stop_356_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___y_366_; 
v___x_364_ = lean_array_uget_borrowed(v_as_354_, v_i_355_);
switch(lean_obj_tag(v___x_364_))
{
case 0:
{
lean_object* v_code_368_; 
v_code_368_ = lean_ctor_get(v___x_364_, 2);
lean_inc_ref(v_code_368_);
v___y_366_ = v_code_368_;
goto v___jp_365_;
}
case 1:
{
lean_object* v_code_369_; 
v_code_369_ = lean_ctor_get(v___x_364_, 1);
lean_inc_ref(v_code_369_);
v___y_366_ = v_code_369_;
goto v___jp_365_;
}
default: 
{
lean_object* v_code_370_; 
v_code_370_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_code_370_);
v___y_366_ = v_code_370_;
goto v___jp_365_;
}
}
v___jp_365_:
{
if (lean_obj_tag(v___y_366_) == 6)
{
lean_dec_ref_known(v___y_366_, 1);
v___y_359_ = v_b_357_;
goto v___jp_358_;
}
else
{
lean_object* v___x_367_; 
lean_dec_ref(v___y_366_);
lean_inc(v___x_364_);
v___x_367_ = lean_array_push(v_b_357_, v___x_364_);
v___y_359_ = v___x_367_;
goto v___jp_358_;
}
}
}
else
{
return v_b_357_;
}
v___jp_358_:
{
size_t v___x_360_; size_t v___x_361_; 
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_355_, v___x_360_);
v_i_355_ = v___x_361_;
v_b_357_ = v___y_359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___boxed(lean_object* v_as_371_, lean_object* v_i_372_, lean_object* v_stop_373_, lean_object* v_b_374_){
_start:
{
size_t v_i_boxed_375_; size_t v_stop_boxed_376_; lean_object* v_res_377_; 
v_i_boxed_375_ = lean_unbox_usize(v_i_372_);
lean_dec(v_i_372_);
v_stop_boxed_376_ = lean_unbox_usize(v_stop_373_);
lean_dec(v_stop_373_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_as_371_, v_i_boxed_375_, v_stop_boxed_376_, v_b_374_);
lean_dec_ref(v_as_371_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(lean_object* v_alts_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_array_get_size(v_alts_378_);
v___x_381_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0));
v___x_382_ = lean_nat_dec_lt(v___x_379_, v___x_380_);
if (v___x_382_ == 0)
{
return v___x_381_;
}
else
{
size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; 
v___x_383_ = ((size_t)0ULL);
v___x_384_ = lean_usize_of_nat(v___x_380_);
v___x_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_378_, v___x_383_, v___x_384_, v___x_381_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable___boxed(lean_object* v_alts_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(v_alts_386_);
lean_dec_ref(v_alts_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(lean_object* v_c_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_typeName_394_; lean_object* v_resultType_395_; lean_object* v_discr_396_; lean_object* v_alts_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_445_; 
v_typeName_394_ = lean_ctor_get(v_c_388_, 0);
v_resultType_395_ = lean_ctor_get(v_c_388_, 1);
v_discr_396_ = lean_ctor_get(v_c_388_, 2);
v_alts_397_ = lean_ctor_get(v_c_388_, 3);
v_isSharedCheck_445_ = !lean_is_exclusive(v_c_388_);
if (v_isSharedCheck_445_ == 0)
{
v___x_399_ = v_c_388_;
v_isShared_400_ = v_isSharedCheck_445_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_alts_397_);
lean_inc(v_discr_396_);
lean_inc(v_resultType_395_);
lean_inc(v_typeName_394_);
lean_dec(v_c_388_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_445_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_alts_401_; lean_object* v___x_402_; 
v_alts_401_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(v_alts_397_);
lean_dec_ref(v_alts_397_);
v___x_402_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(v_alts_401_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_436_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_436_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_436_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_436_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_array_get_size(v_a_403_);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_nat_dec_eq(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_dec_eq(v___x_407_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_413_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 3, v_a_403_);
v___x_413_ = v___x_399_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_typeName_394_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_resultType_395_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_discr_396_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_a_403_);
v___x_413_ = v_reuseFailAlloc_418_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_414_);
v___x_416_ = v___x_405_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
lean_object* v___x_419_; 
lean_del_object(v___x_399_);
lean_dec(v_discr_396_);
lean_dec_ref(v_resultType_395_);
lean_dec(v_typeName_394_);
v___x_419_ = lean_array_fget(v_a_403_, v___x_408_);
lean_dec(v_a_403_);
switch(lean_obj_tag(v___x_419_))
{
case 0:
{
lean_object* v_code_420_; lean_object* v___x_422_; 
v_code_420_ = lean_ctor_get(v___x_419_, 2);
lean_inc_ref(v_code_420_);
lean_dec_ref_known(v___x_419_, 3);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v_code_420_);
v___x_422_ = v___x_405_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_code_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
case 1:
{
lean_object* v_code_424_; lean_object* v___x_426_; 
v_code_424_ = lean_ctor_get(v___x_419_, 1);
lean_inc_ref(v_code_424_);
lean_dec_ref_known(v___x_419_, 2);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v_code_424_);
v___x_426_ = v___x_405_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_code_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
default: 
{
lean_object* v_code_428_; lean_object* v___x_430_; 
v_code_428_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_code_428_);
lean_dec_ref_known(v___x_419_, 1);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v_code_428_);
v___x_430_ = v___x_405_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_code_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_434_; 
lean_dec(v_a_403_);
lean_del_object(v___x_399_);
lean_dec(v_discr_396_);
lean_dec(v_typeName_394_);
v___x_432_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_432_, 0, v_resultType_395_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_432_);
v___x_434_ = v___x_405_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_del_object(v___x_399_);
lean_dec(v_discr_396_);
lean_dec_ref(v_resultType_395_);
lean_dec(v_typeName_394_);
v_a_437_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_402_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_402_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases___boxed(lean_object* v_c_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(v_c_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(lean_object* v_alt_453_, lean_object* v_f_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___y_461_; 
switch(lean_obj_tag(v_alt_453_))
{
case 0:
{
lean_object* v_code_480_; 
v_code_480_ = lean_ctor_get(v_alt_453_, 2);
lean_inc_ref(v_code_480_);
v___y_461_ = v_code_480_;
goto v___jp_460_;
}
case 1:
{
lean_object* v_code_481_; 
v_code_481_ = lean_ctor_get(v_alt_453_, 1);
lean_inc_ref(v_code_481_);
v___y_461_ = v_code_481_;
goto v___jp_460_;
}
default: 
{
lean_object* v_code_482_; 
v_code_482_ = lean_ctor_get(v_alt_453_, 0);
lean_inc_ref(v_code_482_);
v___y_461_ = v_code_482_;
goto v___jp_460_;
}
}
v___jp_460_:
{
lean_object* v___x_462_; 
lean_inc(v___y_458_);
lean_inc_ref(v___y_457_);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
v___x_462_ = lean_apply_6(v_f_454_, v___y_461_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, lean_box(0));
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_471_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_471_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_453_, v_a_463_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_467_);
v___x_469_ = v___x_465_;
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
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_alt_453_);
v_a_472_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_462_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_462_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg___boxed(lean_object* v_alt_483_, lean_object* v_f_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_483_, v_f_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(uint8_t v_pu_491_, lean_object* v_alt_492_, lean_object* v_f_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_492_, v_f_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___boxed(lean_object* v_pu_500_, lean_object* v_alt_501_, lean_object* v_f_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v_pu_boxed_508_; lean_object* v_res_509_; 
v_pu_boxed_508_ = lean_unbox(v_pu_500_);
v_res_509_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(v_pu_boxed_508_, v_alt_501_, v_f_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(lean_object* v_code_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
switch(lean_obj_tag(v_code_510_))
{
case 0:
{
lean_object* v_decl_516_; lean_object* v_k_517_; lean_object* v___x_518_; 
v_decl_516_ = lean_ctor_get(v_code_510_, 0);
v_k_517_ = lean_ctor_get(v_code_510_, 1);
lean_inc_ref(v_k_517_);
v___x_518_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_517_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_541_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_541_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_541_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_541_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_ptr_addr(v_k_517_);
v___x_524_ = lean_ptr_addr(v_a_519_);
v___x_525_ = lean_usize_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_535_; 
lean_inc_ref(v_decl_516_);
v_isSharedCheck_535_ = !lean_is_exclusive(v_code_510_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; lean_object* v_unused_537_; 
v_unused_536_ = lean_ctor_get(v_code_510_, 1);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_code_510_, 0);
lean_dec(v_unused_537_);
v___x_527_ = v_code_510_;
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
else
{
lean_dec(v_code_510_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v_a_519_);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_decl_516_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_a_519_);
v___x_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_530_);
v___x_532_ = v___x_521_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v___x_539_; 
lean_dec(v_a_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v_code_510_);
v___x_539_ = v___x_521_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_code_510_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_510_, 2);
return v___x_518_;
}
}
case 2:
{
lean_object* v_decl_542_; lean_object* v_k_543_; lean_object* v_params_544_; lean_object* v_type_545_; lean_object* v_value_546_; uint8_t v___x_547_; lean_object* v___x_548_; 
v_decl_542_ = lean_ctor_get(v_code_510_, 0);
v_k_543_ = lean_ctor_get(v_code_510_, 1);
v_params_544_ = lean_ctor_get(v_decl_542_, 2);
v_type_545_ = lean_ctor_get(v_decl_542_, 3);
v_value_546_ = lean_ctor_get(v_decl_542_, 4);
v___x_547_ = 1;
lean_inc_ref(v_value_546_);
v___x_548_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_value_546_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
lean_inc_ref(v_params_544_);
lean_inc_ref(v_type_545_);
lean_inc_ref(v_decl_542_);
v___x_550_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_547_, v_decl_542_, v_type_545_, v_params_544_, v_a_549_, v_a_512_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
lean_inc_ref(v_k_543_);
v___x_552_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_543_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_590_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_590_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_590_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_590_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
size_t v___x_557_; size_t v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_ptr_addr(v_k_543_);
v___x_558_ = lean_ptr_addr(v_a_553_);
v___x_559_ = lean_usize_dec_eq(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_569_; 
v_isSharedCheck_569_ = !lean_is_exclusive(v_code_510_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; lean_object* v_unused_571_; 
v_unused_570_ = lean_ctor_get(v_code_510_, 1);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_code_510_, 0);
lean_dec(v_unused_571_);
v___x_561_ = v_code_510_;
v_isShared_562_ = v_isSharedCheck_569_;
goto v_resetjp_560_;
}
else
{
lean_dec(v_code_510_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_569_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v_a_553_);
lean_ctor_set(v___x_561_, 0, v_a_551_);
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_551_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_a_553_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_564_);
v___x_566_ = v___x_555_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
size_t v___x_572_; size_t v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_ptr_addr(v_decl_542_);
v___x_573_ = lean_ptr_addr(v_a_551_);
v___x_574_ = lean_usize_dec_eq(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_584_; 
v_isSharedCheck_584_ = !lean_is_exclusive(v_code_510_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; lean_object* v_unused_586_; 
v_unused_585_ = lean_ctor_get(v_code_510_, 1);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_code_510_, 0);
lean_dec(v_unused_586_);
v___x_576_ = v_code_510_;
v_isShared_577_ = v_isSharedCheck_584_;
goto v_resetjp_575_;
}
else
{
lean_dec(v_code_510_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_584_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 1, v_a_553_);
lean_ctor_set(v___x_576_, 0, v_a_551_);
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_551_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_a_553_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_579_);
v___x_581_ = v___x_555_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v___x_588_; 
lean_dec(v_a_553_);
lean_dec(v_a_551_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v_code_510_);
v___x_588_ = v___x_555_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_code_510_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
else
{
lean_dec(v_a_551_);
lean_dec_ref_known(v_code_510_, 2);
return v___x_552_;
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref_known(v_code_510_, 2);
v_a_591_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_550_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_550_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_510_, 2);
return v___x_548_;
}
}
case 4:
{
lean_object* v_cases_599_; lean_object* v_typeName_600_; lean_object* v_resultType_601_; lean_object* v_discr_602_; lean_object* v_alts_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_622_; 
v_cases_599_ = lean_ctor_get(v_code_510_, 0);
lean_inc_ref(v_cases_599_);
lean_dec_ref_known(v_code_510_, 1);
v_typeName_600_ = lean_ctor_get(v_cases_599_, 0);
v_resultType_601_ = lean_ctor_get(v_cases_599_, 1);
v_discr_602_ = lean_ctor_get(v_cases_599_, 2);
v_alts_603_ = lean_ctor_get(v_cases_599_, 3);
v_isSharedCheck_622_ = !lean_is_exclusive(v_cases_599_);
if (v_isSharedCheck_622_ == 0)
{
v___x_605_ = v_cases_599_;
v_isShared_606_ = v_isSharedCheck_622_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_alts_603_);
lean_inc(v_discr_602_);
lean_inc(v_resultType_601_);
lean_inc(v_typeName_600_);
lean_dec(v_cases_599_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_622_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v___x_607_, v_alts_603_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 3, v_a_609_);
v___x_611_ = v___x_605_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_typeName_600_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_resultType_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_discr_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_a_609_);
v___x_611_ = v_reuseFailAlloc_613_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; 
v___x_612_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(v___x_611_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
return v___x_612_;
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_del_object(v___x_605_);
lean_dec(v_discr_602_);
lean_dec_ref(v_resultType_601_);
lean_dec(v_typeName_600_);
v_a_614_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_608_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_608_);
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
case 7:
{
lean_object* v_fvarId_623_; lean_object* v_i_624_; lean_object* v_y_625_; lean_object* v_k_626_; lean_object* v___x_627_; 
v_fvarId_623_ = lean_ctor_get(v_code_510_, 0);
v_i_624_ = lean_ctor_get(v_code_510_, 1);
v_y_625_ = lean_ctor_get(v_code_510_, 2);
v_k_626_ = lean_ctor_get(v_code_510_, 3);
lean_inc_ref(v_k_626_);
v___x_627_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_626_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_652_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_652_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_652_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_652_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
size_t v___x_632_; size_t v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_ptr_addr(v_k_626_);
v___x_633_ = lean_ptr_addr(v_a_628_);
v___x_634_ = lean_usize_dec_eq(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_644_; 
lean_inc(v_y_625_);
lean_inc(v_i_624_);
lean_inc(v_fvarId_623_);
v_isSharedCheck_644_ = !lean_is_exclusive(v_code_510_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; lean_object* v_unused_646_; lean_object* v_unused_647_; lean_object* v_unused_648_; 
v_unused_645_ = lean_ctor_get(v_code_510_, 3);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_code_510_, 2);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_code_510_, 1);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_code_510_, 0);
lean_dec(v_unused_648_);
v___x_636_ = v_code_510_;
v_isShared_637_ = v_isSharedCheck_644_;
goto v_resetjp_635_;
}
else
{
lean_dec(v_code_510_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_644_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 3, v_a_628_);
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_fvarId_623_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_i_624_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_y_625_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_a_628_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_641_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_639_);
v___x_641_ = v___x_630_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_object* v___x_650_; 
lean_dec(v_a_628_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v_code_510_);
v___x_650_ = v___x_630_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_code_510_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_510_, 4);
return v___x_627_;
}
}
case 8:
{
lean_object* v_fvarId_653_; lean_object* v_i_654_; lean_object* v_y_655_; lean_object* v_k_656_; lean_object* v___x_657_; 
v_fvarId_653_ = lean_ctor_get(v_code_510_, 0);
v_i_654_ = lean_ctor_get(v_code_510_, 1);
v_y_655_ = lean_ctor_get(v_code_510_, 2);
v_k_656_ = lean_ctor_get(v_code_510_, 3);
lean_inc_ref(v_k_656_);
v___x_657_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_656_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_682_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_682_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_682_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_682_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
size_t v___x_662_; size_t v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_ptr_addr(v_k_656_);
v___x_663_ = lean_ptr_addr(v_a_658_);
v___x_664_ = lean_usize_dec_eq(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_674_; 
lean_inc(v_y_655_);
lean_inc(v_i_654_);
lean_inc(v_fvarId_653_);
v_isSharedCheck_674_ = !lean_is_exclusive(v_code_510_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; lean_object* v_unused_676_; lean_object* v_unused_677_; lean_object* v_unused_678_; 
v_unused_675_ = lean_ctor_get(v_code_510_, 3);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v_code_510_, 2);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_code_510_, 1);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_code_510_, 0);
lean_dec(v_unused_678_);
v___x_666_ = v_code_510_;
v_isShared_667_ = v_isSharedCheck_674_;
goto v_resetjp_665_;
}
else
{
lean_dec(v_code_510_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_674_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 3, v_a_658_);
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_fvarId_653_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_i_654_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v_y_655_);
lean_ctor_set(v_reuseFailAlloc_673_, 3, v_a_658_);
v___x_669_ = v_reuseFailAlloc_673_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_671_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_669_);
v___x_671_ = v___x_660_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v_a_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v_code_510_);
v___x_680_ = v___x_660_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_code_510_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_510_, 4);
return v___x_657_;
}
}
case 9:
{
lean_object* v_fvarId_683_; lean_object* v_i_684_; lean_object* v_offset_685_; lean_object* v_y_686_; lean_object* v_ty_687_; lean_object* v_k_688_; lean_object* v___x_689_; 
v_fvarId_683_ = lean_ctor_get(v_code_510_, 0);
v_i_684_ = lean_ctor_get(v_code_510_, 1);
v_offset_685_ = lean_ctor_get(v_code_510_, 2);
v_y_686_ = lean_ctor_get(v_code_510_, 3);
v_ty_687_ = lean_ctor_get(v_code_510_, 4);
v_k_688_ = lean_ctor_get(v_code_510_, 5);
lean_inc_ref(v_k_688_);
v___x_689_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_688_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_716_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_716_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_716_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_716_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
size_t v___x_694_; size_t v___x_695_; uint8_t v___x_696_; 
v___x_694_ = lean_ptr_addr(v_k_688_);
v___x_695_ = lean_ptr_addr(v_a_690_);
v___x_696_ = lean_usize_dec_eq(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_706_; 
lean_inc_ref(v_ty_687_);
lean_inc(v_y_686_);
lean_inc(v_offset_685_);
lean_inc(v_i_684_);
lean_inc(v_fvarId_683_);
v_isSharedCheck_706_ = !lean_is_exclusive(v_code_510_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; lean_object* v_unused_712_; 
v_unused_707_ = lean_ctor_get(v_code_510_, 5);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_code_510_, 4);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_code_510_, 3);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_code_510_, 2);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_code_510_, 1);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_code_510_, 0);
lean_dec(v_unused_712_);
v___x_698_ = v_code_510_;
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
else
{
lean_dec(v_code_510_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 5, v_a_690_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_fvarId_683_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_i_684_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_offset_685_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_y_686_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v_ty_687_);
lean_ctor_set(v_reuseFailAlloc_705_, 5, v_a_690_);
v___x_701_ = v_reuseFailAlloc_705_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_703_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_701_);
v___x_703_ = v___x_692_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v___x_714_; 
lean_dec(v_a_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_code_510_);
v___x_714_ = v___x_692_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_code_510_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_510_, 6);
return v___x_689_;
}
}
case 10:
{
lean_object* v_fvarId_717_; lean_object* v_cidx_718_; lean_object* v_k_719_; lean_object* v___x_720_; 
v_fvarId_717_ = lean_ctor_get(v_code_510_, 0);
v_cidx_718_ = lean_ctor_get(v_code_510_, 1);
v_k_719_ = lean_ctor_get(v_code_510_, 2);
lean_inc_ref(v_k_719_);
v___x_720_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_719_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_744_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_744_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_744_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_744_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
size_t v___x_725_; size_t v___x_726_; uint8_t v___x_727_; 
v___x_725_ = lean_ptr_addr(v_k_719_);
v___x_726_ = lean_ptr_addr(v_a_721_);
v___x_727_ = lean_usize_dec_eq(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_737_; 
lean_inc(v_cidx_718_);
lean_inc(v_fvarId_717_);
v_isSharedCheck_737_ = !lean_is_exclusive(v_code_510_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; lean_object* v_unused_739_; lean_object* v_unused_740_; 
v_unused_738_ = lean_ctor_get(v_code_510_, 2);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_code_510_, 1);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_code_510_, 0);
lean_dec(v_unused_740_);
v___x_729_ = v_code_510_;
v_isShared_730_ = v_isSharedCheck_737_;
goto v_resetjp_728_;
}
else
{
lean_dec(v_code_510_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_737_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 2, v_a_721_);
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_fvarId_717_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_cidx_718_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_a_721_);
v___x_732_ = v_reuseFailAlloc_736_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_732_);
v___x_734_ = v___x_723_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v___x_742_; 
lean_dec(v_a_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v_code_510_);
v___x_742_ = v___x_723_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_code_510_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_510_, 3);
return v___x_720_;
}
}
case 11:
{
lean_object* v_fvarId_745_; lean_object* v_n_746_; uint8_t v_check_747_; uint8_t v_persistent_748_; lean_object* v_k_749_; lean_object* v___x_750_; 
v_fvarId_745_ = lean_ctor_get(v_code_510_, 0);
v_n_746_ = lean_ctor_get(v_code_510_, 1);
v_check_747_ = lean_ctor_get_uint8(v_code_510_, sizeof(void*)*3);
v_persistent_748_ = lean_ctor_get_uint8(v_code_510_, sizeof(void*)*3 + 1);
v_k_749_ = lean_ctor_get(v_code_510_, 2);
lean_inc_ref(v_k_749_);
v___x_750_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_749_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_774_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_774_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_774_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_774_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
size_t v___x_755_; size_t v___x_756_; uint8_t v___x_757_; 
v___x_755_ = lean_ptr_addr(v_k_749_);
v___x_756_ = lean_ptr_addr(v_a_751_);
v___x_757_ = lean_usize_dec_eq(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_767_; 
lean_inc(v_n_746_);
lean_inc(v_fvarId_745_);
v_isSharedCheck_767_ = !lean_is_exclusive(v_code_510_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; lean_object* v_unused_769_; lean_object* v_unused_770_; 
v_unused_768_ = lean_ctor_get(v_code_510_, 2);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_code_510_, 1);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_code_510_, 0);
lean_dec(v_unused_770_);
v___x_759_ = v_code_510_;
v_isShared_760_ = v_isSharedCheck_767_;
goto v_resetjp_758_;
}
else
{
lean_dec(v_code_510_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_767_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 2, v_a_751_);
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_fvarId_745_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_n_746_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v_a_751_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*3, v_check_747_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*3 + 1, v_persistent_748_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_762_);
v___x_764_ = v___x_753_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v___x_772_; 
lean_dec(v_a_751_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_code_510_);
v___x_772_ = v___x_753_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_code_510_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_510_, 3);
return v___x_750_;
}
}
case 12:
{
lean_object* v_fvarId_775_; lean_object* v_n_776_; uint8_t v_check_777_; uint8_t v_persistent_778_; lean_object* v_objs_x3f_779_; lean_object* v_k_780_; lean_object* v___x_781_; 
v_fvarId_775_ = lean_ctor_get(v_code_510_, 0);
v_n_776_ = lean_ctor_get(v_code_510_, 1);
v_check_777_ = lean_ctor_get_uint8(v_code_510_, sizeof(void*)*4);
v_persistent_778_ = lean_ctor_get_uint8(v_code_510_, sizeof(void*)*4 + 1);
v_objs_x3f_779_ = lean_ctor_get(v_code_510_, 2);
v_k_780_ = lean_ctor_get(v_code_510_, 3);
lean_inc_ref(v_k_780_);
v___x_781_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_780_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_806_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_806_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_806_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_806_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
size_t v___x_786_; size_t v___x_787_; uint8_t v___x_788_; 
v___x_786_ = lean_ptr_addr(v_k_780_);
v___x_787_ = lean_ptr_addr(v_a_782_);
v___x_788_ = lean_usize_dec_eq(v___x_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_798_; 
lean_inc(v_objs_x3f_779_);
lean_inc(v_n_776_);
lean_inc(v_fvarId_775_);
v_isSharedCheck_798_ = !lean_is_exclusive(v_code_510_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_799_ = lean_ctor_get(v_code_510_, 3);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_code_510_, 2);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_code_510_, 1);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_code_510_, 0);
lean_dec(v_unused_802_);
v___x_790_ = v_code_510_;
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
else
{
lean_dec(v_code_510_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 3, v_a_782_);
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_fvarId_775_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_n_776_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_objs_x3f_779_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v_a_782_);
lean_ctor_set_uint8(v_reuseFailAlloc_797_, sizeof(void*)*4, v_check_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_797_, sizeof(void*)*4 + 1, v_persistent_778_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_793_);
v___x_795_ = v___x_784_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
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
else
{
lean_object* v___x_804_; 
lean_dec(v_a_782_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v_code_510_);
v___x_804_ = v___x_784_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_code_510_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_510_, 4);
return v___x_781_;
}
}
case 13:
{
lean_object* v_fvarId_807_; lean_object* v_k_808_; lean_object* v___x_809_; 
v_fvarId_807_ = lean_ctor_get(v_code_510_, 0);
v_k_808_ = lean_ctor_get(v_code_510_, 1);
lean_inc_ref(v_k_808_);
v___x_809_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_808_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_832_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_832_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_832_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_832_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
size_t v___x_814_; size_t v___x_815_; uint8_t v___x_816_; 
v___x_814_ = lean_ptr_addr(v_k_808_);
v___x_815_ = lean_ptr_addr(v_a_810_);
v___x_816_ = lean_usize_dec_eq(v___x_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_826_; 
lean_inc(v_fvarId_807_);
v_isSharedCheck_826_ = !lean_is_exclusive(v_code_510_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; lean_object* v_unused_828_; 
v_unused_827_ = lean_ctor_get(v_code_510_, 1);
lean_dec(v_unused_827_);
v_unused_828_ = lean_ctor_get(v_code_510_, 0);
lean_dec(v_unused_828_);
v___x_818_ = v_code_510_;
v_isShared_819_ = v_isSharedCheck_826_;
goto v_resetjp_817_;
}
else
{
lean_dec(v_code_510_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_826_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v_a_810_);
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_fvarId_807_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_a_810_);
v___x_821_ = v_reuseFailAlloc_825_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_823_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_821_);
v___x_823_ = v___x_812_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
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
else
{
lean_object* v___x_830_; 
lean_dec(v_a_810_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v_code_510_);
v___x_830_ = v___x_812_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_code_510_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_510_, 2);
return v___x_809_;
}
}
default: 
{
lean_object* v___x_833_; 
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v_code_510_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed(lean_object* v_code_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_code_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(lean_object* v_i_841_, lean_object* v_as_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_array_get_size(v_as_842_);
v___x_849_ = lean_nat_dec_lt(v_i_841_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec(v_i_841_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v_as_842_);
return v___x_850_;
}
else
{
lean_object* v___f_851_; lean_object* v_a_852_; lean_object* v___x_853_; 
v___f_851_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed), 6, 0);
v_a_852_ = lean_array_fget_borrowed(v_as_842_, v_i_841_);
lean_inc(v_a_852_);
v___x_853_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_a_852_, v___f_851_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; size_t v___x_855_; size_t v___x_856_; uint8_t v___x_857_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = lean_ptr_addr(v_a_852_);
v___x_856_ = lean_ptr_addr(v_a_854_);
v___x_857_ = lean_usize_dec_eq(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = lean_nat_add(v_i_841_, v___x_858_);
v___x_860_ = lean_array_fset(v_as_842_, v_i_841_, v_a_854_);
lean_dec(v_i_841_);
v_i_841_ = v___x_859_;
v_as_842_ = v___x_860_;
goto _start;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v_a_854_);
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = lean_nat_add(v_i_841_, v___x_862_);
lean_dec(v_i_841_);
v_i_841_ = v___x_863_;
goto _start;
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v_as_842_);
lean_dec(v_i_841_);
v_a_865_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_853_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_853_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1___boxed(lean_object* v_i_873_, lean_object* v_as_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v_i_873_, v_as_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(lean_object* v_f_881_, lean_object* v_v_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
if (lean_obj_tag(v_v_882_) == 0)
{
lean_object* v_code_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_912_; 
v_code_888_ = lean_ctor_get(v_v_882_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v_v_882_);
if (v_isSharedCheck_912_ == 0)
{
v___x_890_ = v_v_882_;
v_isShared_891_ = v_isSharedCheck_912_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_code_888_);
lean_dec(v_v_882_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_912_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; 
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
v___x_892_ = lean_apply_6(v_f_881_, v_code_888_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, lean_box(0));
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_903_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_903_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v_a_893_);
v___x_898_ = v___x_890_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_902_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_898_);
v___x_900_ = v___x_895_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_del_object(v___x_890_);
v_a_904_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_892_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_892_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
else
{
lean_object* v___x_913_; 
lean_dec_ref(v_f_881_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v_v_882_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg___boxed(lean_object* v_f_914_, lean_object* v_v_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_914_, v_v_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(uint8_t v_pu_922_, lean_object* v_f_923_, lean_object* v_v_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_923_, v_v_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___boxed(lean_object* v_pu_931_, lean_object* v_f_932_, lean_object* v_v_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
uint8_t v_pu_boxed_939_; lean_object* v_res_940_; 
v_pu_boxed_939_ = lean_unbox(v_pu_931_);
v_res_940_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(v_pu_boxed_939_, v_f_932_, v_v_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(lean_object* v_decl_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_toSignature_948_; lean_object* v_value_949_; uint8_t v_recursive_950_; lean_object* v_inlineAttr_x3f_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_976_; 
v_toSignature_948_ = lean_ctor_get(v_decl_942_, 0);
v_value_949_ = lean_ctor_get(v_decl_942_, 1);
v_recursive_950_ = lean_ctor_get_uint8(v_decl_942_, sizeof(void*)*3);
v_inlineAttr_x3f_951_ = lean_ctor_get(v_decl_942_, 2);
v_isSharedCheck_976_ = !lean_is_exclusive(v_decl_942_);
if (v_isSharedCheck_976_ == 0)
{
v___x_953_ = v_decl_942_;
v_isShared_954_ = v_isSharedCheck_976_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_inlineAttr_x3f_951_);
lean_inc(v_value_949_);
lean_inc(v_toSignature_948_);
lean_dec(v_decl_942_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_976_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___f_955_; lean_object* v___x_956_; 
v___f_955_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0));
v___x_956_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v___f_955_, v_value_949_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_967_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_967_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_a_957_);
v___x_962_ = v___x_953_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_toSignature_948_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_a_957_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_inlineAttr_x3f_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3, v_recursive_950_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_962_);
v___x_964_ = v___x_959_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_del_object(v___x_953_);
lean_dec(v_inlineAttr_x3f_951_);
lean_dec_ref(v_toSignature_948_);
v_a_968_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_956_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_956_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed(lean_object* v_decl_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(v_decl_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
return v_res_983_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(lean_object* v_as_984_, size_t v_i_985_, size_t v_stop_986_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_usize_dec_eq(v_i_985_, v_stop_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
v___x_988_ = lean_array_uget_borrowed(v_as_984_, v_i_985_);
if (lean_obj_tag(v___x_988_) == 2)
{
uint8_t v___x_989_; 
v___x_989_ = 1;
return v___x_989_;
}
else
{
size_t v___x_990_; size_t v___x_991_; 
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_985_, v___x_990_);
v_i_985_ = v___x_991_;
goto _start;
}
}
else
{
uint8_t v___x_993_; 
v___x_993_ = 0;
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0___boxed(lean_object* v_as_994_, lean_object* v_i_995_, lean_object* v_stop_996_){
_start:
{
size_t v_i_boxed_997_; size_t v_stop_boxed_998_; uint8_t v_res_999_; lean_object* v_r_1000_; 
v_i_boxed_997_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_stop_boxed_998_ = lean_unbox_usize(v_stop_996_);
lean_dec(v_stop_996_);
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_as_994_, v_i_boxed_997_, v_stop_boxed_998_);
lean_dec_ref(v_as_994_);
v_r_1000_ = lean_box(v_res_999_);
return v_r_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureHasDefault(lean_object* v_alts_1001_){
_start:
{
lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1020_; 
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_array_get_size(v_alts_1001_);
v___x_1020_ = lean_nat_dec_lt(v___x_1007_, v___x_1008_);
if (v___x_1020_ == 0)
{
goto v___jp_1009_;
}
else
{
if (v___x_1020_ == 0)
{
goto v___jp_1009_;
}
else
{
size_t v___x_1021_; size_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1021_ = ((size_t)0ULL);
v___x_1022_ = lean_usize_of_nat(v___x_1008_);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_alts_1001_, v___x_1021_, v___x_1022_);
if (v___x_1023_ == 0)
{
goto v___jp_1009_;
}
else
{
return v_alts_1001_;
}
}
}
v___jp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___y_1004_);
v___x_1006_ = lean_array_push(v___y_1003_, v___x_1005_);
return v___x_1006_;
}
v___jp_1009_:
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(2u);
v___x_1011_ = lean_nat_dec_lt(v___x_1008_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_last_1015_; lean_object* v_alts_1016_; 
v___x_1012_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0, &l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
v___x_1013_ = lean_unsigned_to_nat(1u);
v___x_1014_ = lean_nat_sub(v___x_1008_, v___x_1013_);
v_last_1015_ = lean_array_get(v___x_1012_, v_alts_1001_, v___x_1014_);
lean_dec(v___x_1014_);
v_alts_1016_ = lean_array_pop(v_alts_1001_);
switch(lean_obj_tag(v_last_1015_))
{
case 0:
{
lean_object* v_code_1017_; 
v_code_1017_ = lean_ctor_get(v_last_1015_, 2);
lean_inc_ref(v_code_1017_);
lean_dec_ref_known(v_last_1015_, 3);
v___y_1003_ = v_alts_1016_;
v___y_1004_ = v_code_1017_;
goto v___jp_1002_;
}
case 1:
{
lean_object* v_code_1018_; 
v_code_1018_ = lean_ctor_get(v_last_1015_, 1);
lean_inc_ref(v_code_1018_);
lean_dec_ref_known(v_last_1015_, 2);
v___y_1003_ = v_alts_1016_;
v___y_1004_ = v_code_1018_;
goto v___jp_1002_;
}
default: 
{
lean_object* v_code_1019_; 
v_code_1019_ = lean_ctor_get(v_last_1015_, 0);
lean_inc_ref(v_code_1019_);
lean_dec_ref_known(v_last_1015_, 1);
v___y_1003_ = v_alts_1016_;
v___y_1004_ = v_code_1019_;
goto v___jp_1002_;
}
}
}
else
{
return v_alts_1001_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpCase___closed__3(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = ((lean_object*)(l_Lean_Compiler_LCNF_simpCase___closed__2));
v___x_1030_ = 2;
v___x_1031_ = ((lean_object*)(l_Lean_Compiler_LCNF_simpCase___closed__1));
v___x_1032_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1031_, v___x_1030_, v___x_1029_, v___x_1028_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpCase(void){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_obj_once(&l_Lean_Compiler_LCNF_simpCase___closed__3, &l_Lean_Compiler_LCNF_simpCase___closed__3_once, _init_l_Lean_Compiler_LCNF_simpCase___closed__3);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1104_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_));
v___x_1105_ = 1;
v___x_1106_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_));
v___x_1107_ = l_Lean_registerTraceClass(v___x_1104_, v___x_1105_, v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2____boxed(lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
return v_res_1109_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_SimpCase(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_simpCase = _init_l_Lean_Compiler_LCNF_simpCase();
lean_mark_persistent(l_Lean_Compiler_LCNF_simpCase);
res = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_SimpCase(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_SimpCase(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_SimpCase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_SimpCase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_SimpCase(builtin);
}
#ifdef __cplusplus
}
#endif
