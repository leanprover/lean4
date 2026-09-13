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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___x_1677__overap_166_; lean_object* v___x_167_; 
v___x_162_ = l_StateRefT_x27_instMonad___redArg(v___x_161_);
v___x_163_ = lean_box(0);
v___x_164_ = l_instInhabitedOfMonad___redArg(v___x_162_, v___x_163_);
v___f_165_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_165_, 0, v___x_164_);
v___x_1677__overap_166_ = lean_panic_fn_borrowed(v___f_165_, v_msg_131_);
lean_dec_ref(v___f_165_);
lean_inc(v___y_135_);
lean_inc_ref(v___y_134_);
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
v___x_167_ = lean_apply_5(v___x_1677__overap_166_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, lean_box(0));
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
uint8_t v___x_383_; 
v___x_383_ = lean_nat_dec_le(v___x_380_, v___x_380_);
if (v___x_383_ == 0)
{
if (v___x_382_ == 0)
{
return v___x_381_;
}
else
{
size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
v___x_384_ = ((size_t)0ULL);
v___x_385_ = lean_usize_of_nat(v___x_380_);
v___x_386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_378_, v___x_384_, v___x_385_, v___x_381_);
return v___x_386_;
}
}
else
{
size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((size_t)0ULL);
v___x_388_ = lean_usize_of_nat(v___x_380_);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_378_, v___x_387_, v___x_388_, v___x_381_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable___boxed(lean_object* v_alts_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(v_alts_390_);
lean_dec_ref(v_alts_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(lean_object* v_c_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_typeName_398_; lean_object* v_resultType_399_; lean_object* v_discr_400_; lean_object* v_alts_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_449_; 
v_typeName_398_ = lean_ctor_get(v_c_392_, 0);
v_resultType_399_ = lean_ctor_get(v_c_392_, 1);
v_discr_400_ = lean_ctor_get(v_c_392_, 2);
v_alts_401_ = lean_ctor_get(v_c_392_, 3);
v_isSharedCheck_449_ = !lean_is_exclusive(v_c_392_);
if (v_isSharedCheck_449_ == 0)
{
v___x_403_ = v_c_392_;
v_isShared_404_ = v_isSharedCheck_449_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_alts_401_);
lean_inc(v_discr_400_);
lean_inc(v_resultType_399_);
lean_inc(v_typeName_398_);
lean_dec(v_c_392_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_449_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_alts_405_; lean_object* v___x_406_; 
v_alts_405_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(v_alts_401_);
lean_dec_ref(v_alts_401_);
v___x_406_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(v_alts_405_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_440_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_440_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_440_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_440_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_411_ = lean_array_get_size(v_a_407_);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_nat_dec_eq(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_dec_eq(v___x_411_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_417_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 3, v_a_407_);
v___x_417_ = v___x_403_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_typeName_398_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_resultType_399_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_discr_400_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_a_407_);
v___x_417_ = v_reuseFailAlloc_422_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_418_);
v___x_420_ = v___x_409_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
else
{
lean_object* v___x_423_; 
lean_del_object(v___x_403_);
lean_dec(v_discr_400_);
lean_dec_ref(v_resultType_399_);
lean_dec(v_typeName_398_);
v___x_423_ = lean_array_fget(v_a_407_, v___x_412_);
lean_dec(v_a_407_);
switch(lean_obj_tag(v___x_423_))
{
case 0:
{
lean_object* v_code_424_; lean_object* v___x_426_; 
v_code_424_ = lean_ctor_get(v___x_423_, 2);
lean_inc_ref(v_code_424_);
lean_dec_ref_known(v___x_423_, 3);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v_code_424_);
v___x_426_ = v___x_409_;
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
case 1:
{
lean_object* v_code_428_; lean_object* v___x_430_; 
v_code_428_ = lean_ctor_get(v___x_423_, 1);
lean_inc_ref(v_code_428_);
lean_dec_ref_known(v___x_423_, 2);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v_code_428_);
v___x_430_ = v___x_409_;
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
default: 
{
lean_object* v_code_432_; lean_object* v___x_434_; 
v_code_432_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_code_432_);
lean_dec_ref_known(v___x_423_, 1);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v_code_432_);
v___x_434_ = v___x_409_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_code_432_);
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
}
else
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_dec(v_a_407_);
lean_del_object(v___x_403_);
lean_dec(v_discr_400_);
lean_dec(v_typeName_398_);
v___x_436_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_436_, 0, v_resultType_399_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_436_);
v___x_438_ = v___x_409_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_del_object(v___x_403_);
lean_dec(v_discr_400_);
lean_dec_ref(v_resultType_399_);
lean_dec(v_typeName_398_);
v_a_441_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_406_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_406_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases___boxed(lean_object* v_c_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(v_c_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(lean_object* v_alt_457_, lean_object* v_f_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___y_465_; 
switch(lean_obj_tag(v_alt_457_))
{
case 0:
{
lean_object* v_code_484_; 
v_code_484_ = lean_ctor_get(v_alt_457_, 2);
lean_inc_ref(v_code_484_);
v___y_465_ = v_code_484_;
goto v___jp_464_;
}
case 1:
{
lean_object* v_code_485_; 
v_code_485_ = lean_ctor_get(v_alt_457_, 1);
lean_inc_ref(v_code_485_);
v___y_465_ = v_code_485_;
goto v___jp_464_;
}
default: 
{
lean_object* v_code_486_; 
v_code_486_ = lean_ctor_get(v_alt_457_, 0);
lean_inc_ref(v_code_486_);
v___y_465_ = v_code_486_;
goto v___jp_464_;
}
}
v___jp_464_:
{
lean_object* v___x_466_; 
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
lean_inc(v___y_460_);
lean_inc_ref(v___y_459_);
v___x_466_ = lean_apply_6(v_f_458_, v___y_465_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, lean_box(0));
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_475_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_475_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_457_, v_a_467_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v_alt_457_);
v_a_476_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_466_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_466_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg___boxed(lean_object* v_alt_487_, lean_object* v_f_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_487_, v_f_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(uint8_t v_pu_495_, lean_object* v_alt_496_, lean_object* v_f_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_496_, v_f_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___boxed(lean_object* v_pu_504_, lean_object* v_alt_505_, lean_object* v_f_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
uint8_t v_pu_boxed_512_; lean_object* v_res_513_; 
v_pu_boxed_512_ = lean_unbox(v_pu_504_);
v_res_513_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(v_pu_boxed_512_, v_alt_505_, v_f_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(lean_object* v_code_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
switch(lean_obj_tag(v_code_514_))
{
case 0:
{
lean_object* v_decl_520_; lean_object* v_k_521_; lean_object* v___x_522_; 
v_decl_520_ = lean_ctor_get(v_code_514_, 0);
v_k_521_ = lean_ctor_get(v_code_514_, 1);
lean_inc_ref(v_k_521_);
v___x_522_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_521_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_545_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_545_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_545_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_545_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
size_t v___x_527_; size_t v___x_528_; uint8_t v___x_529_; 
v___x_527_ = lean_ptr_addr(v_k_521_);
v___x_528_ = lean_ptr_addr(v_a_523_);
v___x_529_ = lean_usize_dec_eq(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_539_; 
lean_inc_ref(v_decl_520_);
v_isSharedCheck_539_ = !lean_is_exclusive(v_code_514_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; lean_object* v_unused_541_; 
v_unused_540_ = lean_ctor_get(v_code_514_, 1);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_code_514_, 0);
lean_dec(v_unused_541_);
v___x_531_ = v_code_514_;
v_isShared_532_ = v_isSharedCheck_539_;
goto v_resetjp_530_;
}
else
{
lean_dec(v_code_514_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_539_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v_a_523_);
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_decl_520_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_a_523_);
v___x_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_534_);
v___x_536_ = v___x_525_;
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
}
else
{
lean_object* v___x_543_; 
lean_dec(v_a_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v_code_514_);
v___x_543_ = v___x_525_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_code_514_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_514_, 2);
return v___x_522_;
}
}
case 2:
{
lean_object* v_decl_546_; lean_object* v_k_547_; lean_object* v_params_548_; lean_object* v_type_549_; lean_object* v_value_550_; uint8_t v___x_551_; lean_object* v___x_552_; 
v_decl_546_ = lean_ctor_get(v_code_514_, 0);
v_k_547_ = lean_ctor_get(v_code_514_, 1);
v_params_548_ = lean_ctor_get(v_decl_546_, 2);
v_type_549_ = lean_ctor_get(v_decl_546_, 3);
v_value_550_ = lean_ctor_get(v_decl_546_, 4);
v___x_551_ = 1;
lean_inc_ref(v_value_550_);
v___x_552_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_value_550_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
lean_inc_ref(v_params_548_);
lean_inc_ref(v_type_549_);
lean_inc_ref(v_decl_546_);
v___x_554_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_551_, v_decl_546_, v_type_549_, v_params_548_, v_a_553_, v_a_516_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_556_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
lean_inc_ref(v_k_547_);
v___x_556_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_547_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_594_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_594_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_594_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_594_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
size_t v___x_561_; size_t v___x_562_; uint8_t v___x_563_; 
v___x_561_ = lean_ptr_addr(v_k_547_);
v___x_562_ = lean_ptr_addr(v_a_557_);
v___x_563_ = lean_usize_dec_eq(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_573_; 
v_isSharedCheck_573_ = !lean_is_exclusive(v_code_514_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_574_ = lean_ctor_get(v_code_514_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_code_514_, 0);
lean_dec(v_unused_575_);
v___x_565_ = v_code_514_;
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
else
{
lean_dec(v_code_514_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_a_557_);
lean_ctor_set(v___x_565_, 0, v_a_555_);
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_555_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_a_557_);
v___x_568_ = v_reuseFailAlloc_572_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_568_);
v___x_570_ = v___x_559_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
else
{
size_t v___x_576_; size_t v___x_577_; uint8_t v___x_578_; 
v___x_576_ = lean_ptr_addr(v_decl_546_);
v___x_577_ = lean_ptr_addr(v_a_555_);
v___x_578_ = lean_usize_dec_eq(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_588_; 
v_isSharedCheck_588_ = !lean_is_exclusive(v_code_514_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; lean_object* v_unused_590_; 
v_unused_589_ = lean_ctor_get(v_code_514_, 1);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_code_514_, 0);
lean_dec(v_unused_590_);
v___x_580_ = v_code_514_;
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
else
{
lean_dec(v_code_514_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_a_557_);
lean_ctor_set(v___x_580_, 0, v_a_555_);
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_555_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_a_557_);
v___x_583_ = v_reuseFailAlloc_587_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_585_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_583_);
v___x_585_ = v___x_559_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v___x_592_; 
lean_dec(v_a_557_);
lean_dec(v_a_555_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v_code_514_);
v___x_592_ = v___x_559_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_code_514_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
else
{
lean_dec(v_a_555_);
lean_dec_ref_known(v_code_514_, 2);
return v___x_556_;
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref_known(v_code_514_, 2);
v_a_595_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_554_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_554_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_514_, 2);
return v___x_552_;
}
}
case 4:
{
lean_object* v_cases_603_; lean_object* v_typeName_604_; lean_object* v_resultType_605_; lean_object* v_discr_606_; lean_object* v_alts_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_626_; 
v_cases_603_ = lean_ctor_get(v_code_514_, 0);
lean_inc_ref(v_cases_603_);
lean_dec_ref_known(v_code_514_, 1);
v_typeName_604_ = lean_ctor_get(v_cases_603_, 0);
v_resultType_605_ = lean_ctor_get(v_cases_603_, 1);
v_discr_606_ = lean_ctor_get(v_cases_603_, 2);
v_alts_607_ = lean_ctor_get(v_cases_603_, 3);
v_isSharedCheck_626_ = !lean_is_exclusive(v_cases_603_);
if (v_isSharedCheck_626_ == 0)
{
v___x_609_ = v_cases_603_;
v_isShared_610_ = v_isSharedCheck_626_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_alts_607_);
lean_inc(v_discr_606_);
lean_inc(v_resultType_605_);
lean_inc(v_typeName_604_);
lean_dec(v_cases_603_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_626_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v___x_611_, v_alts_607_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 3, v_a_613_);
v___x_615_ = v___x_609_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_typeName_604_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_resultType_605_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_discr_606_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_a_613_);
v___x_615_ = v_reuseFailAlloc_617_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; 
v___x_616_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(v___x_615_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
return v___x_616_;
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_del_object(v___x_609_);
lean_dec(v_discr_606_);
lean_dec_ref(v_resultType_605_);
lean_dec(v_typeName_604_);
v_a_618_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_612_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_612_);
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
case 7:
{
lean_object* v_fvarId_627_; lean_object* v_i_628_; lean_object* v_y_629_; lean_object* v_k_630_; lean_object* v___x_631_; 
v_fvarId_627_ = lean_ctor_get(v_code_514_, 0);
v_i_628_ = lean_ctor_get(v_code_514_, 1);
v_y_629_ = lean_ctor_get(v_code_514_, 2);
v_k_630_ = lean_ctor_get(v_code_514_, 3);
lean_inc_ref(v_k_630_);
v___x_631_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_630_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_656_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_656_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_656_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_656_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
size_t v___x_636_; size_t v___x_637_; uint8_t v___x_638_; 
v___x_636_ = lean_ptr_addr(v_k_630_);
v___x_637_ = lean_ptr_addr(v_a_632_);
v___x_638_ = lean_usize_dec_eq(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_648_; 
lean_inc(v_y_629_);
lean_inc(v_i_628_);
lean_inc(v_fvarId_627_);
v_isSharedCheck_648_ = !lean_is_exclusive(v_code_514_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; 
v_unused_649_ = lean_ctor_get(v_code_514_, 3);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v_code_514_, 2);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_code_514_, 1);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_code_514_, 0);
lean_dec(v_unused_652_);
v___x_640_ = v_code_514_;
v_isShared_641_ = v_isSharedCheck_648_;
goto v_resetjp_639_;
}
else
{
lean_dec(v_code_514_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_648_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 3, v_a_632_);
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_fvarId_627_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_i_628_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_y_629_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_a_632_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_643_);
v___x_645_ = v___x_634_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v___x_654_; 
lean_dec(v_a_632_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v_code_514_);
v___x_654_ = v___x_634_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_code_514_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_514_, 4);
return v___x_631_;
}
}
case 8:
{
lean_object* v_fvarId_657_; lean_object* v_i_658_; lean_object* v_y_659_; lean_object* v_k_660_; lean_object* v___x_661_; 
v_fvarId_657_ = lean_ctor_get(v_code_514_, 0);
v_i_658_ = lean_ctor_get(v_code_514_, 1);
v_y_659_ = lean_ctor_get(v_code_514_, 2);
v_k_660_ = lean_ctor_get(v_code_514_, 3);
lean_inc_ref(v_k_660_);
v___x_661_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_660_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_686_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_686_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_686_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_686_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
size_t v___x_666_; size_t v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_ptr_addr(v_k_660_);
v___x_667_ = lean_ptr_addr(v_a_662_);
v___x_668_ = lean_usize_dec_eq(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_678_; 
lean_inc(v_y_659_);
lean_inc(v_i_658_);
lean_inc(v_fvarId_657_);
v_isSharedCheck_678_ = !lean_is_exclusive(v_code_514_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; 
v_unused_679_ = lean_ctor_get(v_code_514_, 3);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_code_514_, 2);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_code_514_, 1);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_code_514_, 0);
lean_dec(v_unused_682_);
v___x_670_ = v_code_514_;
v_isShared_671_ = v_isSharedCheck_678_;
goto v_resetjp_669_;
}
else
{
lean_dec(v_code_514_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_678_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 3, v_a_662_);
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_fvarId_657_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_i_658_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_y_659_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_a_662_);
v___x_673_ = v_reuseFailAlloc_677_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_675_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_673_);
v___x_675_ = v___x_664_;
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
lean_object* v___x_684_; 
lean_dec(v_a_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v_code_514_);
v___x_684_ = v___x_664_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_code_514_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_514_, 4);
return v___x_661_;
}
}
case 9:
{
lean_object* v_fvarId_687_; lean_object* v_i_688_; lean_object* v_offset_689_; lean_object* v_y_690_; lean_object* v_ty_691_; lean_object* v_k_692_; lean_object* v___x_693_; 
v_fvarId_687_ = lean_ctor_get(v_code_514_, 0);
v_i_688_ = lean_ctor_get(v_code_514_, 1);
v_offset_689_ = lean_ctor_get(v_code_514_, 2);
v_y_690_ = lean_ctor_get(v_code_514_, 3);
v_ty_691_ = lean_ctor_get(v_code_514_, 4);
v_k_692_ = lean_ctor_get(v_code_514_, 5);
lean_inc_ref(v_k_692_);
v___x_693_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_692_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_720_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_720_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_720_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_720_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
size_t v___x_698_; size_t v___x_699_; uint8_t v___x_700_; 
v___x_698_ = lean_ptr_addr(v_k_692_);
v___x_699_ = lean_ptr_addr(v_a_694_);
v___x_700_ = lean_usize_dec_eq(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_710_; 
lean_inc_ref(v_ty_691_);
lean_inc(v_y_690_);
lean_inc(v_offset_689_);
lean_inc(v_i_688_);
lean_inc(v_fvarId_687_);
v_isSharedCheck_710_ = !lean_is_exclusive(v_code_514_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; lean_object* v_unused_712_; lean_object* v_unused_713_; lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; 
v_unused_711_ = lean_ctor_get(v_code_514_, 5);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_code_514_, 4);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_code_514_, 3);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_code_514_, 2);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_code_514_, 1);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_code_514_, 0);
lean_dec(v_unused_716_);
v___x_702_ = v_code_514_;
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
else
{
lean_dec(v_code_514_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 5, v_a_694_);
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_fvarId_687_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_i_688_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_offset_689_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_y_690_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v_ty_691_);
lean_ctor_set(v_reuseFailAlloc_709_, 5, v_a_694_);
v___x_705_ = v_reuseFailAlloc_709_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_705_);
v___x_707_ = v___x_696_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v___x_718_; 
lean_dec(v_a_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v_code_514_);
v___x_718_ = v___x_696_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_code_514_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_514_, 6);
return v___x_693_;
}
}
case 10:
{
lean_object* v_fvarId_721_; lean_object* v_cidx_722_; lean_object* v_k_723_; lean_object* v___x_724_; 
v_fvarId_721_ = lean_ctor_get(v_code_514_, 0);
v_cidx_722_ = lean_ctor_get(v_code_514_, 1);
v_k_723_ = lean_ctor_get(v_code_514_, 2);
lean_inc_ref(v_k_723_);
v___x_724_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_723_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_748_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_748_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_748_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_748_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
size_t v___x_729_; size_t v___x_730_; uint8_t v___x_731_; 
v___x_729_ = lean_ptr_addr(v_k_723_);
v___x_730_ = lean_ptr_addr(v_a_725_);
v___x_731_ = lean_usize_dec_eq(v___x_729_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_741_; 
lean_inc(v_cidx_722_);
lean_inc(v_fvarId_721_);
v_isSharedCheck_741_ = !lean_is_exclusive(v_code_514_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; lean_object* v_unused_743_; lean_object* v_unused_744_; 
v_unused_742_ = lean_ctor_get(v_code_514_, 2);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v_code_514_, 1);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v_code_514_, 0);
lean_dec(v_unused_744_);
v___x_733_ = v_code_514_;
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
else
{
lean_dec(v_code_514_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 2, v_a_725_);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_fvarId_721_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_cidx_722_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_a_725_);
v___x_736_ = v_reuseFailAlloc_740_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_738_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_736_);
v___x_738_ = v___x_727_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_object* v___x_746_; 
lean_dec(v_a_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v_code_514_);
v___x_746_ = v___x_727_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_code_514_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_514_, 3);
return v___x_724_;
}
}
case 11:
{
lean_object* v_fvarId_749_; lean_object* v_n_750_; uint8_t v_check_751_; uint8_t v_persistent_752_; lean_object* v_k_753_; lean_object* v___x_754_; 
v_fvarId_749_ = lean_ctor_get(v_code_514_, 0);
v_n_750_ = lean_ctor_get(v_code_514_, 1);
v_check_751_ = lean_ctor_get_uint8(v_code_514_, sizeof(void*)*3);
v_persistent_752_ = lean_ctor_get_uint8(v_code_514_, sizeof(void*)*3 + 1);
v_k_753_ = lean_ctor_get(v_code_514_, 2);
lean_inc_ref(v_k_753_);
v___x_754_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_753_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_778_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_778_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_778_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_778_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
size_t v___x_759_; size_t v___x_760_; uint8_t v___x_761_; 
v___x_759_ = lean_ptr_addr(v_k_753_);
v___x_760_ = lean_ptr_addr(v_a_755_);
v___x_761_ = lean_usize_dec_eq(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_771_; 
lean_inc(v_n_750_);
lean_inc(v_fvarId_749_);
v_isSharedCheck_771_ = !lean_is_exclusive(v_code_514_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; lean_object* v_unused_773_; lean_object* v_unused_774_; 
v_unused_772_ = lean_ctor_get(v_code_514_, 2);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v_code_514_, 1);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_code_514_, 0);
lean_dec(v_unused_774_);
v___x_763_ = v_code_514_;
v_isShared_764_ = v_isSharedCheck_771_;
goto v_resetjp_762_;
}
else
{
lean_dec(v_code_514_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_771_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v_a_755_);
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_fvarId_749_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_n_750_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_a_755_);
lean_ctor_set_uint8(v_reuseFailAlloc_770_, sizeof(void*)*3, v_check_751_);
lean_ctor_set_uint8(v_reuseFailAlloc_770_, sizeof(void*)*3 + 1, v_persistent_752_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_766_);
v___x_768_ = v___x_757_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v___x_776_; 
lean_dec(v_a_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v_code_514_);
v___x_776_ = v___x_757_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_code_514_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_514_, 3);
return v___x_754_;
}
}
case 12:
{
lean_object* v_fvarId_779_; lean_object* v_n_780_; uint8_t v_check_781_; uint8_t v_persistent_782_; lean_object* v_objs_x3f_783_; lean_object* v_k_784_; lean_object* v___x_785_; 
v_fvarId_779_ = lean_ctor_get(v_code_514_, 0);
v_n_780_ = lean_ctor_get(v_code_514_, 1);
v_check_781_ = lean_ctor_get_uint8(v_code_514_, sizeof(void*)*4);
v_persistent_782_ = lean_ctor_get_uint8(v_code_514_, sizeof(void*)*4 + 1);
v_objs_x3f_783_ = lean_ctor_get(v_code_514_, 2);
v_k_784_ = lean_ctor_get(v_code_514_, 3);
lean_inc_ref(v_k_784_);
v___x_785_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_784_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_810_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_810_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_810_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_810_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
size_t v___x_790_; size_t v___x_791_; uint8_t v___x_792_; 
v___x_790_ = lean_ptr_addr(v_k_784_);
v___x_791_ = lean_ptr_addr(v_a_786_);
v___x_792_ = lean_usize_dec_eq(v___x_790_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_802_; 
lean_inc(v_objs_x3f_783_);
lean_inc(v_n_780_);
lean_inc(v_fvarId_779_);
v_isSharedCheck_802_ = !lean_is_exclusive(v_code_514_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; 
v_unused_803_ = lean_ctor_get(v_code_514_, 3);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_code_514_, 2);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_code_514_, 1);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_code_514_, 0);
lean_dec(v_unused_806_);
v___x_794_ = v_code_514_;
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
else
{
lean_dec(v_code_514_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 3, v_a_786_);
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_fvarId_779_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_n_780_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_objs_x3f_783_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_a_786_);
lean_ctor_set_uint8(v_reuseFailAlloc_801_, sizeof(void*)*4, v_check_781_);
lean_ctor_set_uint8(v_reuseFailAlloc_801_, sizeof(void*)*4 + 1, v_persistent_782_);
v___x_797_ = v_reuseFailAlloc_801_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_799_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_797_);
v___x_799_ = v___x_788_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v___x_808_; 
lean_dec(v_a_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_code_514_);
v___x_808_ = v___x_788_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_code_514_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_514_, 4);
return v___x_785_;
}
}
case 13:
{
lean_object* v_fvarId_811_; lean_object* v_k_812_; lean_object* v___x_813_; 
v_fvarId_811_ = lean_ctor_get(v_code_514_, 0);
v_k_812_ = lean_ctor_get(v_code_514_, 1);
lean_inc_ref(v_k_812_);
v___x_813_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_812_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_836_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_836_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_836_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_836_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
size_t v___x_818_; size_t v___x_819_; uint8_t v___x_820_; 
v___x_818_ = lean_ptr_addr(v_k_812_);
v___x_819_ = lean_ptr_addr(v_a_814_);
v___x_820_ = lean_usize_dec_eq(v___x_818_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_830_; 
lean_inc(v_fvarId_811_);
v_isSharedCheck_830_ = !lean_is_exclusive(v_code_514_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; lean_object* v_unused_832_; 
v_unused_831_ = lean_ctor_get(v_code_514_, 1);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_code_514_, 0);
lean_dec(v_unused_832_);
v___x_822_ = v_code_514_;
v_isShared_823_ = v_isSharedCheck_830_;
goto v_resetjp_821_;
}
else
{
lean_dec(v_code_514_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_830_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_a_814_);
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_fvarId_811_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_a_814_);
v___x_825_ = v_reuseFailAlloc_829_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_827_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_825_);
v___x_827_ = v___x_816_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v___x_834_; 
lean_dec(v_a_814_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v_code_514_);
v___x_834_ = v___x_816_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_code_514_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_514_, 2);
return v___x_813_;
}
}
default: 
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v_code_514_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed(lean_object* v_code_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_code_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(lean_object* v_i_845_, lean_object* v_as_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_852_ = lean_array_get_size(v_as_846_);
v___x_853_ = lean_nat_dec_lt(v_i_845_, v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
lean_dec(v_i_845_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_as_846_);
return v___x_854_;
}
else
{
lean_object* v___f_855_; lean_object* v_a_856_; lean_object* v___x_857_; 
v___f_855_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed), 6, 0);
v_a_856_ = lean_array_fget_borrowed(v_as_846_, v_i_845_);
lean_inc(v_a_856_);
v___x_857_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_a_856_, v___f_855_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; size_t v___x_859_; size_t v___x_860_; uint8_t v___x_861_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = lean_ptr_addr(v_a_856_);
v___x_860_ = lean_ptr_addr(v_a_858_);
v___x_861_ = lean_usize_dec_eq(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = lean_nat_add(v_i_845_, v___x_862_);
v___x_864_ = lean_array_fset(v_as_846_, v_i_845_, v_a_858_);
lean_dec(v_i_845_);
v_i_845_ = v___x_863_;
v_as_846_ = v___x_864_;
goto _start;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v_a_858_);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_nat_add(v_i_845_, v___x_866_);
lean_dec(v_i_845_);
v_i_845_ = v___x_867_;
goto _start;
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref(v_as_846_);
lean_dec(v_i_845_);
v_a_869_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_857_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_857_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1___boxed(lean_object* v_i_877_, lean_object* v_as_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v_i_877_, v_as_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(lean_object* v_f_885_, lean_object* v_v_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
if (lean_obj_tag(v_v_886_) == 0)
{
lean_object* v_code_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_916_; 
v_code_892_ = lean_ctor_get(v_v_886_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v_v_886_);
if (v_isSharedCheck_916_ == 0)
{
v___x_894_ = v_v_886_;
v_isShared_895_ = v_isSharedCheck_916_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_code_892_);
lean_dec(v_v_886_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_916_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; 
lean_inc(v___y_890_);
lean_inc_ref(v___y_889_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
v___x_896_ = lean_apply_6(v_f_885_, v_code_892_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, lean_box(0));
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_907_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_907_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_a_897_);
v___x_902_ = v___x_894_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_906_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_902_);
v___x_904_ = v___x_899_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_del_object(v___x_894_);
v_a_908_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_896_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_896_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
lean_object* v___x_917_; 
lean_dec_ref(v_f_885_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v_v_886_);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg___boxed(lean_object* v_f_918_, lean_object* v_v_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_918_, v_v_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(uint8_t v_pu_926_, lean_object* v_f_927_, lean_object* v_v_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_927_, v_v_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___boxed(lean_object* v_pu_935_, lean_object* v_f_936_, lean_object* v_v_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
uint8_t v_pu_boxed_943_; lean_object* v_res_944_; 
v_pu_boxed_943_ = lean_unbox(v_pu_935_);
v_res_944_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(v_pu_boxed_943_, v_f_936_, v_v_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(lean_object* v_decl_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_toSignature_952_; lean_object* v_value_953_; uint8_t v_recursive_954_; lean_object* v_inlineAttr_x3f_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_980_; 
v_toSignature_952_ = lean_ctor_get(v_decl_946_, 0);
v_value_953_ = lean_ctor_get(v_decl_946_, 1);
v_recursive_954_ = lean_ctor_get_uint8(v_decl_946_, sizeof(void*)*3);
v_inlineAttr_x3f_955_ = lean_ctor_get(v_decl_946_, 2);
v_isSharedCheck_980_ = !lean_is_exclusive(v_decl_946_);
if (v_isSharedCheck_980_ == 0)
{
v___x_957_ = v_decl_946_;
v_isShared_958_ = v_isSharedCheck_980_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_inlineAttr_x3f_955_);
lean_inc(v_value_953_);
lean_inc(v_toSignature_952_);
lean_dec(v_decl_946_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_980_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___f_959_; lean_object* v___x_960_; 
v___f_959_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0));
v___x_960_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v___f_959_, v_value_953_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_971_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_971_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_971_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_971_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_a_961_);
v___x_966_ = v___x_957_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_toSignature_952_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_a_961_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_inlineAttr_x3f_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*3, v_recursive_954_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_966_);
v___x_968_ = v___x_963_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_del_object(v___x_957_);
lean_dec(v_inlineAttr_x3f_955_);
lean_dec_ref(v_toSignature_952_);
v_a_972_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_960_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_960_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed(lean_object* v_decl_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(v_decl_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
return v_res_987_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(lean_object* v_as_988_, size_t v_i_989_, size_t v_stop_990_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = lean_usize_dec_eq(v_i_989_, v_stop_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_array_uget_borrowed(v_as_988_, v_i_989_);
if (lean_obj_tag(v___x_992_) == 2)
{
uint8_t v___x_993_; 
v___x_993_ = 1;
return v___x_993_;
}
else
{
size_t v___x_994_; size_t v___x_995_; 
v___x_994_ = ((size_t)1ULL);
v___x_995_ = lean_usize_add(v_i_989_, v___x_994_);
v_i_989_ = v___x_995_;
goto _start;
}
}
else
{
uint8_t v___x_997_; 
v___x_997_ = 0;
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0___boxed(lean_object* v_as_998_, lean_object* v_i_999_, lean_object* v_stop_1000_){
_start:
{
size_t v_i_boxed_1001_; size_t v_stop_boxed_1002_; uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_i_boxed_1001_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_stop_boxed_1002_ = lean_unbox_usize(v_stop_1000_);
lean_dec(v_stop_1000_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_as_998_, v_i_boxed_1001_, v_stop_boxed_1002_);
lean_dec_ref(v_as_998_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureHasDefault(lean_object* v_alts_1005_){
_start:
{
lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1024_; 
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_array_get_size(v_alts_1005_);
v___x_1024_ = lean_nat_dec_lt(v___x_1011_, v___x_1012_);
if (v___x_1024_ == 0)
{
goto v___jp_1013_;
}
else
{
if (v___x_1024_ == 0)
{
goto v___jp_1013_;
}
else
{
size_t v___x_1025_; size_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = lean_usize_of_nat(v___x_1012_);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_alts_1005_, v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
goto v___jp_1013_;
}
else
{
return v_alts_1005_;
}
}
}
v___jp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___y_1008_);
v___x_1010_ = lean_array_push(v___y_1007_, v___x_1009_);
return v___x_1010_;
}
v___jp_1013_:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_unsigned_to_nat(2u);
v___x_1015_ = lean_nat_dec_lt(v___x_1012_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_last_1019_; lean_object* v_alts_1020_; 
v___x_1016_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0, &l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_nat_sub(v___x_1012_, v___x_1017_);
v_last_1019_ = lean_array_get(v___x_1016_, v_alts_1005_, v___x_1018_);
lean_dec(v___x_1018_);
v_alts_1020_ = lean_array_pop(v_alts_1005_);
switch(lean_obj_tag(v_last_1019_))
{
case 0:
{
lean_object* v_code_1021_; 
v_code_1021_ = lean_ctor_get(v_last_1019_, 2);
lean_inc_ref(v_code_1021_);
lean_dec_ref_known(v_last_1019_, 3);
v___y_1007_ = v_alts_1020_;
v___y_1008_ = v_code_1021_;
goto v___jp_1006_;
}
case 1:
{
lean_object* v_code_1022_; 
v_code_1022_ = lean_ctor_get(v_last_1019_, 1);
lean_inc_ref(v_code_1022_);
lean_dec_ref_known(v_last_1019_, 2);
v___y_1007_ = v_alts_1020_;
v___y_1008_ = v_code_1022_;
goto v___jp_1006_;
}
default: 
{
lean_object* v_code_1023_; 
v_code_1023_ = lean_ctor_get(v_last_1019_, 0);
lean_inc_ref(v_code_1023_);
lean_dec_ref_known(v_last_1019_, 1);
v___y_1007_ = v_alts_1020_;
v___y_1008_ = v_code_1023_;
goto v___jp_1006_;
}
}
}
else
{
return v_alts_1005_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpCase___closed__3(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = ((lean_object*)(l_Lean_Compiler_LCNF_simpCase___closed__2));
v___x_1034_ = 2;
v___x_1035_ = ((lean_object*)(l_Lean_Compiler_LCNF_simpCase___closed__1));
v___x_1036_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1035_, v___x_1034_, v___x_1033_, v___x_1032_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpCase(void){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_obj_once(&l_Lean_Compiler_LCNF_simpCase___closed__3, &l_Lean_Compiler_LCNF_simpCase___closed__3_once, _init_l_Lean_Compiler_LCNF_simpCase___closed__3);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1108_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_));
v___x_1109_ = 1;
v___x_1110_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_));
v___x_1111_ = l_Lean_registerTraceClass(v___x_1108_, v___x_1109_, v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2____boxed(lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
return v_res_1113_;
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
