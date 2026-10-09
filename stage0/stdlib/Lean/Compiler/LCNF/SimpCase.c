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
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_131_ = stack[0].m_obj;
lean_object* v___y_132_ = stack[1].m_obj;
lean_object* v___y_133_ = stack[2].m_obj;
lean_object* v___y_134_ = stack[3].m_obj;
lean_object* v___y_135_ = stack[4].m_obj;
lean_object* v_res_174_;
v_res_174_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v_msg_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___boxed(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v_msg_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_181_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2));
v___x_186_ = lean_unsigned_to_nat(36u);
v___x_187_ = lean_unsigned_to_nat(77u);
v___x_188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1));
v___x_189_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0));
v___x_190_ = l_mkPanicMessageWithDecl(v___x_189_, v___x_188_, v___x_187_, v___x_186_, v___x_185_);
return v___x_190_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(lean_object* v_snd_191_, lean_object* v_fst_192_, lean_object* v_as_193_, size_t v_sz_194_, size_t v_i_195_, lean_object* v_b_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_a_203_; uint8_t v___x_207_; 
v___x_207_ = lean_usize_dec_lt(v_i_195_, v_sz_194_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_dec_ref(v_fst_192_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v_b_196_);
return v___x_208_;
}
else
{
lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_259_; 
v_fst_209_ = lean_ctor_get(v_b_196_, 0);
v_snd_210_ = lean_ctor_get(v_b_196_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_b_196_);
if (v_isSharedCheck_259_ == 0)
{
v___x_212_ = v_b_196_;
v_isShared_213_ = v_isSharedCheck_259_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_snd_210_);
lean_inc(v_fst_209_);
lean_dec(v_b_196_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_259_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; uint8_t v_first_215_; lean_object* v_a_221_; uint8_t v___x_222_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_252_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v_first_215_ = lean_nat_dec_eq(v_snd_191_, v___x_214_);
v_a_221_ = lean_array_uget_borrowed(v_as_193_, v_i_195_);
v___x_222_ = 1;
switch(lean_obj_tag(v_a_221_))
{
case 0:
{
lean_object* v_code_256_; 
v_code_256_ = lean_ctor_get(v_a_221_, 2);
lean_inc_ref(v_code_256_);
v___y_252_ = v_code_256_;
goto v___jp_251_;
}
case 1:
{
lean_object* v_code_257_; 
v_code_257_ = lean_ctor_get(v_a_221_, 1);
lean_inc_ref(v_code_257_);
v___y_252_ = v_code_257_;
goto v___jp_251_;
}
default: 
{
lean_object* v_code_258_; 
v_code_258_ = lean_ctor_get(v_a_221_, 0);
lean_inc_ref(v_code_258_);
v___y_252_ = v_code_258_;
goto v___jp_251_;
}
}
v___jp_216_:
{
lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_217_ = lean_box(v_first_215_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_217_);
v___x_219_ = v___x_212_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_fst_209_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
v_a_203_ = v___x_219_;
goto v___jp_202_;
}
}
v___jp_223_:
{
uint8_t v___x_226_; 
v___x_226_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_222_, v___y_224_, v___y_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_del_object(v___x_212_);
lean_inc(v_a_221_);
v___x_227_ = lean_array_push(v_fst_209_, v_a_221_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_snd_210_);
v_a_203_ = v___x_228_;
goto v___jp_202_;
}
else
{
if (lean_obj_tag(v_a_221_) == 1)
{
uint8_t v___x_229_; 
v___x_229_ = lean_unbox(v_snd_210_);
lean_dec(v_snd_210_);
if (v___x_229_ == 0)
{
lean_object* v_code_230_; lean_object* v___x_231_; 
v_code_230_ = lean_ctor_get(v_a_221_, 1);
v___x_231_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_222_, v_code_230_, v___y_198_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_dec_ref_known(v___x_231_, 1);
goto v___jp_216_;
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_del_object(v___x_212_);
lean_dec(v_fst_209_);
lean_dec_ref(v_fst_192_);
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
goto v___jp_216_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_del_object(v___x_212_);
v___x_240_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3);
v___x_241_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v___x_240_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v___x_242_; 
lean_dec_ref_known(v___x_241_, 1);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_fst_209_);
lean_ctor_set(v___x_242_, 1, v_snd_210_);
v_a_203_ = v___x_242_;
goto v___jp_202_;
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec(v_snd_210_);
lean_dec(v_fst_209_);
lean_dec_ref(v_fst_192_);
v_a_243_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_241_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
v___jp_251_:
{
switch(lean_obj_tag(v_fst_192_))
{
case 0:
{
lean_object* v_code_253_; 
v_code_253_ = lean_ctor_get(v_fst_192_, 2);
lean_inc_ref(v_code_253_);
v___y_224_ = v___y_252_;
v___y_225_ = v_code_253_;
goto v___jp_223_;
}
case 1:
{
lean_object* v_code_254_; 
v_code_254_ = lean_ctor_get(v_fst_192_, 1);
lean_inc_ref(v_code_254_);
v___y_224_ = v___y_252_;
v___y_225_ = v_code_254_;
goto v___jp_223_;
}
default: 
{
lean_object* v_code_255_; 
v_code_255_ = lean_ctor_get(v_fst_192_, 0);
lean_inc_ref(v_code_255_);
v___y_224_ = v___y_252_;
v___y_225_ = v_code_255_;
goto v___jp_223_;
}
}
}
}
}
v___jp_202_:
{
size_t v___x_204_; size_t v___x_205_; 
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_add(v_i_195_, v___x_204_);
v_i_195_ = v___x_205_;
v_b_196_ = v_a_203_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_191_ = stack[0].m_obj;
lean_object* v_fst_192_ = stack[1].m_obj;
lean_object* v_as_193_ = stack[2].m_obj;
size_t v_sz_194_ = stack[3].m_num;
size_t v_i_195_ = stack[4].m_num;
lean_object* v_b_196_ = stack[5].m_obj;
lean_object* v___y_197_ = stack[6].m_obj;
lean_object* v___y_198_ = stack[7].m_obj;
lean_object* v___y_199_ = stack[8].m_obj;
lean_object* v___y_200_ = stack[9].m_obj;
lean_object* v_res_260_;
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_191_, v_fst_192_, v_as_193_, v_sz_194_, v_i_195_, v_b_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___boxed(lean_object* v_snd_261_, lean_object* v_fst_262_, lean_object* v_as_263_, lean_object* v_sz_264_, lean_object* v_i_265_, lean_object* v_b_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
size_t v_sz_boxed_272_; size_t v_i_boxed_273_; lean_object* v_res_274_; 
v_sz_boxed_272_ = lean_unbox_usize(v_sz_264_);
lean_dec(v_sz_264_);
v_i_boxed_273_ = lean_unbox_usize(v_i_265_);
lean_dec(v_i_265_);
v_res_274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_261_, v_fst_262_, v_as_263_, v_sz_boxed_272_, v_i_boxed_273_, v_b_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec_ref(v_as_263_);
lean_dec(v_snd_261_);
return v_res_274_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(lean_object* v___x_275_, lean_object* v_as_276_, size_t v_i_277_, size_t v_stop_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = lean_usize_dec_eq(v_i_277_, v_stop_278_);
if (v___x_279_ == 0)
{
uint8_t v___x_280_; lean_object* v___x_281_; 
v___x_280_ = 1;
v___x_281_ = lean_array_uget_borrowed(v_as_276_, v_i_277_);
if (lean_obj_tag(v___x_281_) == 2)
{
return v___x_280_;
}
else
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_dec_le(v___x_275_, v___x_282_);
if (v___x_283_ == 0)
{
size_t v___x_284_; size_t v___x_285_; 
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_add(v_i_277_, v___x_284_);
v_i_277_ = v___x_285_;
goto _start;
}
else
{
return v___x_280_;
}
}
}
else
{
uint8_t v___x_287_; 
v___x_287_ = 0;
return v___x_287_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_275_ = stack[0].m_obj;
lean_object* v_as_276_ = stack[1].m_obj;
size_t v_i_277_ = stack[2].m_num;
size_t v_stop_278_ = stack[3].m_num;
uint8_t v_res_288_;
v_res_288_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(v___x_275_, v_as_276_, v_i_277_, v_stop_278_);
stack->m_num = v_res_288_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2___boxed(lean_object* v___x_289_, lean_object* v_as_290_, lean_object* v_i_291_, lean_object* v_stop_292_){
_start:
{
size_t v_i_boxed_293_; size_t v_stop_boxed_294_; uint8_t v_res_295_; lean_object* v_r_296_; 
v_i_boxed_293_ = lean_unbox_usize(v_i_291_);
lean_dec(v_i_291_);
v_stop_boxed_294_ = lean_unbox_usize(v_stop_292_);
lean_dec(v_stop_292_);
v_res_295_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(v___x_289_, v_as_290_, v_i_boxed_293_, v_stop_boxed_294_);
lean_dec_ref(v_as_290_);
lean_dec(v___x_289_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(lean_object* v_alts_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_342_; 
v___x_315_ = lean_array_get_size(v_alts_303_);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_dec_le(v___x_315_, v___x_316_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_nat_dec_lt(v___x_343_, v___x_315_);
if (v___x_344_ == 0)
{
goto v___jp_317_;
}
else
{
if (v___x_344_ == 0)
{
goto v___jp_317_;
}
else
{
size_t v___x_345_; size_t v___x_346_; uint8_t v___x_347_; 
v___x_345_ = ((size_t)0ULL);
v___x_346_ = lean_usize_of_nat(v___x_315_);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(v___x_315_, v_alts_303_, v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
goto v___jp_317_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v_alts_303_);
return v___x_348_;
}
}
}
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v_alts_303_);
return v___x_349_;
}
v___jp_309_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_312_, 0, v___y_311_);
v___x_313_ = lean_array_push(v___y_310_, v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
v___jp_317_:
{
lean_object* v___x_318_; lean_object* v_fst_319_; lean_object* v_snd_320_; uint8_t v_first_321_; 
v___x_318_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(v_alts_303_);
v_fst_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_fst_319_);
v_snd_320_ = lean_ctor_get(v___x_318_, 1);
lean_inc(v_snd_320_);
lean_dec_ref(v___x_318_);
v_first_321_ = lean_nat_dec_eq(v_snd_320_, v___x_316_);
if (v_first_321_ == 0)
{
lean_object* v___x_322_; size_t v_sz_323_; size_t v___x_324_; lean_object* v___x_325_; 
v___x_322_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1));
v_sz_323_ = lean_array_size(v_alts_303_);
v___x_324_ = ((size_t)0ULL);
lean_inc(v_fst_319_);
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_320_, v_fst_319_, v_alts_303_, v_sz_323_, v___x_324_, v___x_322_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec_ref(v_alts_303_);
lean_dec(v_snd_320_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
switch(lean_obj_tag(v_fst_319_))
{
case 0:
{
lean_object* v_fst_327_; lean_object* v_code_328_; 
v_fst_327_ = lean_ctor_get(v_a_326_, 0);
lean_inc(v_fst_327_);
lean_dec(v_a_326_);
v_code_328_ = lean_ctor_get(v_fst_319_, 2);
lean_inc_ref(v_code_328_);
lean_dec_ref_known(v_fst_319_, 3);
v___y_310_ = v_fst_327_;
v___y_311_ = v_code_328_;
goto v___jp_309_;
}
case 1:
{
lean_object* v_fst_329_; lean_object* v_code_330_; 
v_fst_329_ = lean_ctor_get(v_a_326_, 0);
lean_inc(v_fst_329_);
lean_dec(v_a_326_);
v_code_330_ = lean_ctor_get(v_fst_319_, 1);
lean_inc_ref(v_code_330_);
lean_dec_ref_known(v_fst_319_, 2);
v___y_310_ = v_fst_329_;
v___y_311_ = v_code_330_;
goto v___jp_309_;
}
default: 
{
lean_object* v_fst_331_; lean_object* v_code_332_; 
v_fst_331_ = lean_ctor_get(v_a_326_, 0);
lean_inc(v_fst_331_);
lean_dec(v_a_326_);
v_code_332_ = lean_ctor_get(v_fst_319_, 0);
lean_inc_ref(v_code_332_);
lean_dec_ref_known(v_fst_319_, 1);
v___y_310_ = v_fst_331_;
v___y_311_ = v_code_332_;
goto v___jp_309_;
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec(v_fst_319_);
v_a_333_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_325_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_325_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
else
{
lean_object* v___x_341_; 
lean_dec(v_snd_320_);
lean_dec(v_fst_319_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v_alts_303_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_0interp(lean_interpreter_value* stack)
{
lean_object* v_alts_303_ = stack[0].m_obj;
lean_object* v_a_304_ = stack[1].m_obj;
lean_object* v_a_305_ = stack[2].m_obj;
lean_object* v_a_306_ = stack[3].m_obj;
lean_object* v_a_307_ = stack[4].m_obj;
lean_object* v_res_350_;
v_res_350_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(v_alts_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
stack->m_obj
 = v_res_350_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___boxed(lean_object* v_alts_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(v_alts_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
return v_res_357_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(lean_object* v_as_358_, size_t v_i_359_, size_t v_stop_360_, lean_object* v_b_361_){
_start:
{
lean_object* v___y_363_; uint8_t v___x_367_; 
v___x_367_ = lean_usize_dec_eq(v_i_359_, v_stop_360_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___y_370_; 
v___x_368_ = lean_array_uget_borrowed(v_as_358_, v_i_359_);
switch(lean_obj_tag(v___x_368_))
{
case 0:
{
lean_object* v_code_372_; 
v_code_372_ = lean_ctor_get(v___x_368_, 2);
lean_inc_ref(v_code_372_);
v___y_370_ = v_code_372_;
goto v___jp_369_;
}
case 1:
{
lean_object* v_code_373_; 
v_code_373_ = lean_ctor_get(v___x_368_, 1);
lean_inc_ref(v_code_373_);
v___y_370_ = v_code_373_;
goto v___jp_369_;
}
default: 
{
lean_object* v_code_374_; 
v_code_374_ = lean_ctor_get(v___x_368_, 0);
lean_inc_ref(v_code_374_);
v___y_370_ = v_code_374_;
goto v___jp_369_;
}
}
v___jp_369_:
{
if (lean_obj_tag(v___y_370_) == 6)
{
lean_dec_ref_known(v___y_370_, 1);
v___y_363_ = v_b_361_;
goto v___jp_362_;
}
else
{
lean_object* v___x_371_; 
lean_dec_ref(v___y_370_);
lean_inc(v___x_368_);
v___x_371_ = lean_array_push(v_b_361_, v___x_368_);
v___y_363_ = v___x_371_;
goto v___jp_362_;
}
}
}
else
{
return v_b_361_;
}
v___jp_362_:
{
size_t v___x_364_; size_t v___x_365_; 
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_add(v_i_359_, v___x_364_);
v_i_359_ = v___x_365_;
v_b_361_ = v___y_363_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_358_ = stack[0].m_obj;
size_t v_i_359_ = stack[1].m_num;
size_t v_stop_360_ = stack[2].m_num;
lean_object* v_b_361_ = stack[3].m_obj;
lean_object* v_res_375_;
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_as_358_, v_i_359_, v_stop_360_, v_b_361_);
stack->m_obj
 = v_res_375_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___boxed(lean_object* v_as_376_, lean_object* v_i_377_, lean_object* v_stop_378_, lean_object* v_b_379_){
_start:
{
size_t v_i_boxed_380_; size_t v_stop_boxed_381_; lean_object* v_res_382_; 
v_i_boxed_380_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_stop_boxed_381_ = lean_unbox_usize(v_stop_378_);
lean_dec(v_stop_378_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_as_376_, v_i_boxed_380_, v_stop_boxed_381_, v_b_379_);
lean_dec_ref(v_as_376_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(lean_object* v_alts_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_array_get_size(v_alts_383_);
v___x_386_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0));
v___x_387_ = lean_nat_dec_lt(v___x_384_, v___x_385_);
if (v___x_387_ == 0)
{
return v___x_386_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = lean_nat_dec_le(v___x_385_, v___x_385_);
if (v___x_388_ == 0)
{
if (v___x_387_ == 0)
{
return v___x_386_;
}
else
{
size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; 
v___x_389_ = ((size_t)0ULL);
v___x_390_ = lean_usize_of_nat(v___x_385_);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_383_, v___x_389_, v___x_390_, v___x_386_);
return v___x_391_;
}
}
else
{
size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((size_t)0ULL);
v___x_393_ = lean_usize_of_nat(v___x_385_);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_383_, v___x_392_, v___x_393_, v___x_386_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable___boxed(lean_object* v_alts_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(v_alts_395_);
lean_dec_ref(v_alts_395_);
return v_res_396_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(lean_object* v_c_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_typeName_403_; lean_object* v_resultType_404_; lean_object* v_discr_405_; lean_object* v_alts_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_454_; 
v_typeName_403_ = lean_ctor_get(v_c_397_, 0);
v_resultType_404_ = lean_ctor_get(v_c_397_, 1);
v_discr_405_ = lean_ctor_get(v_c_397_, 2);
v_alts_406_ = lean_ctor_get(v_c_397_, 3);
v_isSharedCheck_454_ = !lean_is_exclusive(v_c_397_);
if (v_isSharedCheck_454_ == 0)
{
v___x_408_ = v_c_397_;
v_isShared_409_ = v_isSharedCheck_454_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_alts_406_);
lean_inc(v_discr_405_);
lean_inc(v_resultType_404_);
lean_inc(v_typeName_403_);
lean_dec(v_c_397_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_454_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_alts_410_; lean_object* v___x_411_; 
v_alts_410_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(v_alts_406_);
lean_dec_ref(v_alts_406_);
v___x_411_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(v_alts_410_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_445_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_445_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_445_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_445_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = lean_array_get_size(v_a_412_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_nat_dec_eq(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = lean_nat_dec_eq(v___x_416_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_422_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 3, v_a_412_);
v___x_422_ = v___x_408_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_typeName_403_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_resultType_404_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_discr_405_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_a_412_);
v___x_422_ = v_reuseFailAlloc_427_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_423_);
v___x_425_ = v___x_414_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
lean_object* v___x_428_; 
lean_del_object(v___x_408_);
lean_dec(v_discr_405_);
lean_dec_ref(v_resultType_404_);
lean_dec(v_typeName_403_);
v___x_428_ = lean_array_fget(v_a_412_, v___x_417_);
lean_dec(v_a_412_);
switch(lean_obj_tag(v___x_428_))
{
case 0:
{
lean_object* v_code_429_; lean_object* v___x_431_; 
v_code_429_ = lean_ctor_get(v___x_428_, 2);
lean_inc_ref(v_code_429_);
lean_dec_ref_known(v___x_428_, 3);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v_code_429_);
v___x_431_ = v___x_414_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_code_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
case 1:
{
lean_object* v_code_433_; lean_object* v___x_435_; 
v_code_433_ = lean_ctor_get(v___x_428_, 1);
lean_inc_ref(v_code_433_);
lean_dec_ref_known(v___x_428_, 2);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v_code_433_);
v___x_435_ = v___x_414_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_code_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
default: 
{
lean_object* v_code_437_; lean_object* v___x_439_; 
v_code_437_ = lean_ctor_get(v___x_428_, 0);
lean_inc_ref(v_code_437_);
lean_dec_ref_known(v___x_428_, 1);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v_code_437_);
v___x_439_ = v___x_414_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_code_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
else
{
lean_object* v___x_441_; lean_object* v___x_443_; 
lean_dec(v_a_412_);
lean_del_object(v___x_408_);
lean_dec(v_discr_405_);
lean_dec(v_typeName_403_);
v___x_441_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_441_, 0, v_resultType_404_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_441_);
v___x_443_ = v___x_414_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_del_object(v___x_408_);
lean_dec(v_discr_405_);
lean_dec_ref(v_resultType_404_);
lean_dec(v_typeName_403_);
v_a_446_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_411_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_411_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_397_ = stack[0].m_obj;
lean_object* v_a_398_ = stack[1].m_obj;
lean_object* v_a_399_ = stack[2].m_obj;
lean_object* v_a_400_ = stack[3].m_obj;
lean_object* v_a_401_ = stack[4].m_obj;
lean_object* v_res_455_;
v_res_455_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(v_c_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
stack->m_obj
 = v_res_455_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases___boxed(lean_object* v_c_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(v_c_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
return v_res_462_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(lean_object* v_alt_463_, lean_object* v_f_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___y_471_; 
switch(lean_obj_tag(v_alt_463_))
{
case 0:
{
lean_object* v_code_490_; 
v_code_490_ = lean_ctor_get(v_alt_463_, 2);
lean_inc_ref(v_code_490_);
v___y_471_ = v_code_490_;
goto v___jp_470_;
}
case 1:
{
lean_object* v_code_491_; 
v_code_491_ = lean_ctor_get(v_alt_463_, 1);
lean_inc_ref(v_code_491_);
v___y_471_ = v_code_491_;
goto v___jp_470_;
}
default: 
{
lean_object* v_code_492_; 
v_code_492_ = lean_ctor_get(v_alt_463_, 0);
lean_inc_ref(v_code_492_);
v___y_471_ = v_code_492_;
goto v___jp_470_;
}
}
v___jp_470_:
{
lean_object* v___x_472_; 
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
v___x_472_ = lean_apply_6(v_f_464_, v___y_471_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, lean_box(0));
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_481_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_463_, v_a_473_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec_ref(v_alt_463_);
v_a_482_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_472_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_472_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_463_ = stack[0].m_obj;
lean_object* v_f_464_ = stack[1].m_obj;
lean_object* v___y_465_ = stack[2].m_obj;
lean_object* v___y_466_ = stack[3].m_obj;
lean_object* v___y_467_ = stack[4].m_obj;
lean_object* v___y_468_ = stack[5].m_obj;
lean_object* v_res_493_;
v_res_493_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_463_, v_f_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg___boxed(lean_object* v_alt_494_, lean_object* v_f_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_494_, v_f_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_501_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(uint8_t v_pu_502_, lean_object* v_alt_503_, lean_object* v_f_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_503_, v_f_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
return v___x_510_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_502_ = stack[0].m_num;
lean_object* v_alt_503_ = stack[1].m_obj;
lean_object* v_f_504_ = stack[2].m_obj;
lean_object* v___y_505_ = stack[3].m_obj;
lean_object* v___y_506_ = stack[4].m_obj;
lean_object* v___y_507_ = stack[5].m_obj;
lean_object* v___y_508_ = stack[6].m_obj;
lean_object* v_res_511_;
v_res_511_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(v_pu_502_, v_alt_503_, v_f_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___boxed(lean_object* v_pu_512_, lean_object* v_alt_513_, lean_object* v_f_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
uint8_t v_pu_boxed_520_; lean_object* v_res_521_; 
v_pu_boxed_520_ = lean_unbox(v_pu_512_);
v_res_521_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(v_pu_boxed_520_, v_alt_513_, v_f_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_521_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(lean_object* v_code_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
switch(lean_obj_tag(v_code_522_))
{
case 0:
{
lean_object* v_decl_528_; lean_object* v_k_529_; lean_object* v___x_530_; 
v_decl_528_ = lean_ctor_get(v_code_522_, 0);
v_k_529_ = lean_ctor_get(v_code_522_, 1);
lean_inc_ref(v_k_529_);
v___x_530_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_529_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_553_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_553_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_553_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_553_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
size_t v___x_535_; size_t v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_ptr_addr(v_k_529_);
v___x_536_ = lean_ptr_addr(v_a_531_);
v___x_537_ = lean_usize_dec_eq(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_547_; 
lean_inc_ref(v_decl_528_);
v_isSharedCheck_547_ = !lean_is_exclusive(v_code_522_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; lean_object* v_unused_549_; 
v_unused_548_ = lean_ctor_get(v_code_522_, 1);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_code_522_, 0);
lean_dec(v_unused_549_);
v___x_539_ = v_code_522_;
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
else
{
lean_dec(v_code_522_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v_a_531_);
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_decl_528_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_a_531_);
v___x_542_ = v_reuseFailAlloc_546_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_544_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_542_);
v___x_544_ = v___x_533_;
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
lean_object* v___x_551_; 
lean_dec(v_a_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v_code_522_);
v___x_551_ = v___x_533_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_code_522_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_522_, 2);
return v___x_530_;
}
}
case 2:
{
lean_object* v_decl_554_; lean_object* v_k_555_; lean_object* v_params_556_; lean_object* v_type_557_; lean_object* v_value_558_; uint8_t v___x_559_; lean_object* v___x_560_; 
v_decl_554_ = lean_ctor_get(v_code_522_, 0);
v_k_555_ = lean_ctor_get(v_code_522_, 1);
v_params_556_ = lean_ctor_get(v_decl_554_, 2);
v_type_557_ = lean_ctor_get(v_decl_554_, 3);
v_value_558_ = lean_ctor_get(v_decl_554_, 4);
v___x_559_ = 1;
lean_inc_ref(v_value_558_);
v___x_560_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_value_558_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_562_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_560_, 1);
lean_inc_ref(v_params_556_);
lean_inc_ref(v_type_557_);
lean_inc_ref(v_decl_554_);
v___x_562_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_559_, v_decl_554_, v_type_557_, v_params_556_, v_a_561_, v_a_524_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_564_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
lean_inc_ref(v_k_555_);
v___x_564_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_555_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_602_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_602_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_602_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_602_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
size_t v___x_569_; size_t v___x_570_; uint8_t v___x_571_; 
v___x_569_ = lean_ptr_addr(v_k_555_);
v___x_570_ = lean_ptr_addr(v_a_565_);
v___x_571_ = lean_usize_dec_eq(v___x_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_581_; 
v_isSharedCheck_581_ = !lean_is_exclusive(v_code_522_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; lean_object* v_unused_583_; 
v_unused_582_ = lean_ctor_get(v_code_522_, 1);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_code_522_, 0);
lean_dec(v_unused_583_);
v___x_573_ = v_code_522_;
v_isShared_574_ = v_isSharedCheck_581_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_code_522_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_581_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v_a_565_);
lean_ctor_set(v___x_573_, 0, v_a_563_);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_563_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_a_565_);
v___x_576_ = v_reuseFailAlloc_580_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_576_);
v___x_578_ = v___x_567_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
size_t v___x_584_; size_t v___x_585_; uint8_t v___x_586_; 
v___x_584_ = lean_ptr_addr(v_decl_554_);
v___x_585_ = lean_ptr_addr(v_a_563_);
v___x_586_ = lean_usize_dec_eq(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_596_; 
v_isSharedCheck_596_ = !lean_is_exclusive(v_code_522_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; lean_object* v_unused_598_; 
v_unused_597_ = lean_ctor_get(v_code_522_, 1);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v_code_522_, 0);
lean_dec(v_unused_598_);
v___x_588_ = v_code_522_;
v_isShared_589_ = v_isSharedCheck_596_;
goto v_resetjp_587_;
}
else
{
lean_dec(v_code_522_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_596_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v_a_565_);
lean_ctor_set(v___x_588_, 0, v_a_563_);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_563_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_a_565_);
v___x_591_ = v_reuseFailAlloc_595_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_593_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_591_);
v___x_593_ = v___x_567_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v___x_600_; 
lean_dec(v_a_565_);
lean_dec(v_a_563_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v_code_522_);
v___x_600_ = v___x_567_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_code_522_);
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
}
else
{
lean_dec(v_a_563_);
lean_dec_ref_known(v_code_522_, 2);
return v___x_564_;
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref_known(v_code_522_, 2);
v_a_603_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_562_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_562_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_522_, 2);
return v___x_560_;
}
}
case 4:
{
lean_object* v_cases_611_; lean_object* v_typeName_612_; lean_object* v_resultType_613_; lean_object* v_discr_614_; lean_object* v_alts_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_634_; 
v_cases_611_ = lean_ctor_get(v_code_522_, 0);
lean_inc_ref(v_cases_611_);
lean_dec_ref_known(v_code_522_, 1);
v_typeName_612_ = lean_ctor_get(v_cases_611_, 0);
v_resultType_613_ = lean_ctor_get(v_cases_611_, 1);
v_discr_614_ = lean_ctor_get(v_cases_611_, 2);
v_alts_615_ = lean_ctor_get(v_cases_611_, 3);
v_isSharedCheck_634_ = !lean_is_exclusive(v_cases_611_);
if (v_isSharedCheck_634_ == 0)
{
v___x_617_ = v_cases_611_;
v_isShared_618_ = v_isSharedCheck_634_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_alts_615_);
lean_inc(v_discr_614_);
lean_inc(v_resultType_613_);
lean_inc(v_typeName_612_);
lean_dec(v_cases_611_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_634_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v___x_619_, v_alts_615_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 3, v_a_621_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_typeName_612_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_resultType_613_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_discr_614_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_a_621_);
v___x_623_ = v_reuseFailAlloc_625_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; 
v___x_624_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(v___x_623_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
return v___x_624_;
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_del_object(v___x_617_);
lean_dec(v_discr_614_);
lean_dec_ref(v_resultType_613_);
lean_dec(v_typeName_612_);
v_a_626_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_620_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_620_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_635_; lean_object* v_i_636_; lean_object* v_y_637_; lean_object* v_k_638_; lean_object* v___x_639_; 
v_fvarId_635_ = lean_ctor_get(v_code_522_, 0);
v_i_636_ = lean_ctor_get(v_code_522_, 1);
v_y_637_ = lean_ctor_get(v_code_522_, 2);
v_k_638_ = lean_ctor_get(v_code_522_, 3);
lean_inc_ref(v_k_638_);
v___x_639_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_638_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_664_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_664_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_664_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_664_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
size_t v___x_644_; size_t v___x_645_; uint8_t v___x_646_; 
v___x_644_ = lean_ptr_addr(v_k_638_);
v___x_645_ = lean_ptr_addr(v_a_640_);
v___x_646_ = lean_usize_dec_eq(v___x_644_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_656_; 
lean_inc(v_y_637_);
lean_inc(v_i_636_);
lean_inc(v_fvarId_635_);
v_isSharedCheck_656_ = !lean_is_exclusive(v_code_522_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; lean_object* v_unused_658_; lean_object* v_unused_659_; lean_object* v_unused_660_; 
v_unused_657_ = lean_ctor_get(v_code_522_, 3);
lean_dec(v_unused_657_);
v_unused_658_ = lean_ctor_get(v_code_522_, 2);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_code_522_, 1);
lean_dec(v_unused_659_);
v_unused_660_ = lean_ctor_get(v_code_522_, 0);
lean_dec(v_unused_660_);
v___x_648_ = v_code_522_;
v_isShared_649_ = v_isSharedCheck_656_;
goto v_resetjp_647_;
}
else
{
lean_dec(v_code_522_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_656_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 3, v_a_640_);
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_fvarId_635_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_i_636_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_y_637_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_a_640_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_651_);
v___x_653_ = v___x_642_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_object* v___x_662_; 
lean_dec(v_a_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_code_522_);
v___x_662_ = v___x_642_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_code_522_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_522_, 4);
return v___x_639_;
}
}
case 8:
{
lean_object* v_fvarId_665_; lean_object* v_i_666_; lean_object* v_y_667_; lean_object* v_k_668_; lean_object* v___x_669_; 
v_fvarId_665_ = lean_ctor_get(v_code_522_, 0);
v_i_666_ = lean_ctor_get(v_code_522_, 1);
v_y_667_ = lean_ctor_get(v_code_522_, 2);
v_k_668_ = lean_ctor_get(v_code_522_, 3);
lean_inc_ref(v_k_668_);
v___x_669_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_668_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_694_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_694_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_694_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_694_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
size_t v___x_674_; size_t v___x_675_; uint8_t v___x_676_; 
v___x_674_ = lean_ptr_addr(v_k_668_);
v___x_675_ = lean_ptr_addr(v_a_670_);
v___x_676_ = lean_usize_dec_eq(v___x_674_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_686_; 
lean_inc(v_y_667_);
lean_inc(v_i_666_);
lean_inc(v_fvarId_665_);
v_isSharedCheck_686_ = !lean_is_exclusive(v_code_522_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; lean_object* v_unused_688_; lean_object* v_unused_689_; lean_object* v_unused_690_; 
v_unused_687_ = lean_ctor_get(v_code_522_, 3);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_code_522_, 2);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_code_522_, 1);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_code_522_, 0);
lean_dec(v_unused_690_);
v___x_678_ = v_code_522_;
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
else
{
lean_dec(v_code_522_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 3, v_a_670_);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_fvarId_665_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_i_666_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_y_667_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_a_670_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_681_);
v___x_683_ = v___x_672_;
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
}
}
else
{
lean_object* v___x_692_; 
lean_dec(v_a_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_code_522_);
v___x_692_ = v___x_672_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_code_522_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_522_, 4);
return v___x_669_;
}
}
case 9:
{
lean_object* v_fvarId_695_; lean_object* v_i_696_; lean_object* v_offset_697_; lean_object* v_y_698_; lean_object* v_ty_699_; lean_object* v_k_700_; lean_object* v___x_701_; 
v_fvarId_695_ = lean_ctor_get(v_code_522_, 0);
v_i_696_ = lean_ctor_get(v_code_522_, 1);
v_offset_697_ = lean_ctor_get(v_code_522_, 2);
v_y_698_ = lean_ctor_get(v_code_522_, 3);
v_ty_699_ = lean_ctor_get(v_code_522_, 4);
v_k_700_ = lean_ctor_get(v_code_522_, 5);
lean_inc_ref(v_k_700_);
v___x_701_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_700_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_728_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_728_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_728_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_728_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
size_t v___x_706_; size_t v___x_707_; uint8_t v___x_708_; 
v___x_706_ = lean_ptr_addr(v_k_700_);
v___x_707_ = lean_ptr_addr(v_a_702_);
v___x_708_ = lean_usize_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_718_; 
lean_inc_ref(v_ty_699_);
lean_inc(v_y_698_);
lean_inc(v_offset_697_);
lean_inc(v_i_696_);
lean_inc(v_fvarId_695_);
v_isSharedCheck_718_ = !lean_is_exclusive(v_code_522_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_719_ = lean_ctor_get(v_code_522_, 5);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_code_522_, 4);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_code_522_, 3);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_code_522_, 2);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_code_522_, 1);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_code_522_, 0);
lean_dec(v_unused_724_);
v___x_710_ = v_code_522_;
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
else
{
lean_dec(v_code_522_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 5, v_a_702_);
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fvarId_695_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_i_696_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_offset_697_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_y_698_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_ty_699_);
lean_ctor_set(v_reuseFailAlloc_717_, 5, v_a_702_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_713_);
v___x_715_ = v___x_704_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v___x_726_; 
lean_dec(v_a_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v_code_522_);
v___x_726_ = v___x_704_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_code_522_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_522_, 6);
return v___x_701_;
}
}
case 10:
{
lean_object* v_fvarId_729_; lean_object* v_cidx_730_; lean_object* v_k_731_; lean_object* v___x_732_; 
v_fvarId_729_ = lean_ctor_get(v_code_522_, 0);
v_cidx_730_ = lean_ctor_get(v_code_522_, 1);
v_k_731_ = lean_ctor_get(v_code_522_, 2);
lean_inc_ref(v_k_731_);
v___x_732_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_731_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_756_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_756_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_756_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_756_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
size_t v___x_737_; size_t v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_ptr_addr(v_k_731_);
v___x_738_ = lean_ptr_addr(v_a_733_);
v___x_739_ = lean_usize_dec_eq(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_749_; 
lean_inc(v_cidx_730_);
lean_inc(v_fvarId_729_);
v_isSharedCheck_749_ = !lean_is_exclusive(v_code_522_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; lean_object* v_unused_751_; lean_object* v_unused_752_; 
v_unused_750_ = lean_ctor_get(v_code_522_, 2);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_code_522_, 1);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_code_522_, 0);
lean_dec(v_unused_752_);
v___x_741_ = v_code_522_;
v_isShared_742_ = v_isSharedCheck_749_;
goto v_resetjp_740_;
}
else
{
lean_dec(v_code_522_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_749_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 2, v_a_733_);
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_fvarId_729_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_cidx_730_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_a_733_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_744_);
v___x_746_ = v___x_735_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
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
lean_object* v___x_754_; 
lean_dec(v_a_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_code_522_);
v___x_754_ = v___x_735_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_code_522_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_522_, 3);
return v___x_732_;
}
}
case 11:
{
lean_object* v_fvarId_757_; lean_object* v_n_758_; uint8_t v_check_759_; uint8_t v_persistent_760_; lean_object* v_k_761_; lean_object* v___x_762_; 
v_fvarId_757_ = lean_ctor_get(v_code_522_, 0);
v_n_758_ = lean_ctor_get(v_code_522_, 1);
v_check_759_ = lean_ctor_get_uint8(v_code_522_, sizeof(void*)*3);
v_persistent_760_ = lean_ctor_get_uint8(v_code_522_, sizeof(void*)*3 + 1);
v_k_761_ = lean_ctor_get(v_code_522_, 2);
lean_inc_ref(v_k_761_);
v___x_762_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_761_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_786_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_786_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_786_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_786_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
size_t v___x_767_; size_t v___x_768_; uint8_t v___x_769_; 
v___x_767_ = lean_ptr_addr(v_k_761_);
v___x_768_ = lean_ptr_addr(v_a_763_);
v___x_769_ = lean_usize_dec_eq(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_779_; 
lean_inc(v_n_758_);
lean_inc(v_fvarId_757_);
v_isSharedCheck_779_ = !lean_is_exclusive(v_code_522_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; lean_object* v_unused_781_; lean_object* v_unused_782_; 
v_unused_780_ = lean_ctor_get(v_code_522_, 2);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v_code_522_, 1);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_code_522_, 0);
lean_dec(v_unused_782_);
v___x_771_ = v_code_522_;
v_isShared_772_ = v_isSharedCheck_779_;
goto v_resetjp_770_;
}
else
{
lean_dec(v_code_522_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_779_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 2, v_a_763_);
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_fvarId_757_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_n_758_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_a_763_);
lean_ctor_set_uint8(v_reuseFailAlloc_778_, sizeof(void*)*3, v_check_759_);
lean_ctor_set_uint8(v_reuseFailAlloc_778_, sizeof(void*)*3 + 1, v_persistent_760_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_774_);
v___x_776_ = v___x_765_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
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
lean_object* v___x_784_; 
lean_dec(v_a_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v_code_522_);
v___x_784_ = v___x_765_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_code_522_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_522_, 3);
return v___x_762_;
}
}
case 12:
{
lean_object* v_fvarId_787_; lean_object* v_n_788_; uint8_t v_check_789_; uint8_t v_persistent_790_; lean_object* v_objs_x3f_791_; lean_object* v_k_792_; lean_object* v___x_793_; 
v_fvarId_787_ = lean_ctor_get(v_code_522_, 0);
v_n_788_ = lean_ctor_get(v_code_522_, 1);
v_check_789_ = lean_ctor_get_uint8(v_code_522_, sizeof(void*)*4);
v_persistent_790_ = lean_ctor_get_uint8(v_code_522_, sizeof(void*)*4 + 1);
v_objs_x3f_791_ = lean_ctor_get(v_code_522_, 2);
v_k_792_ = lean_ctor_get(v_code_522_, 3);
lean_inc_ref(v_k_792_);
v___x_793_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_792_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_818_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_818_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_818_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_818_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
size_t v___x_798_; size_t v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_ptr_addr(v_k_792_);
v___x_799_ = lean_ptr_addr(v_a_794_);
v___x_800_ = lean_usize_dec_eq(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_810_; 
lean_inc(v_objs_x3f_791_);
lean_inc(v_n_788_);
lean_inc(v_fvarId_787_);
v_isSharedCheck_810_ = !lean_is_exclusive(v_code_522_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; lean_object* v_unused_812_; lean_object* v_unused_813_; lean_object* v_unused_814_; 
v_unused_811_ = lean_ctor_get(v_code_522_, 3);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_code_522_, 2);
lean_dec(v_unused_812_);
v_unused_813_ = lean_ctor_get(v_code_522_, 1);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_code_522_, 0);
lean_dec(v_unused_814_);
v___x_802_ = v_code_522_;
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
else
{
lean_dec(v_code_522_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 3, v_a_794_);
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_fvarId_787_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_n_788_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_objs_x3f_791_);
lean_ctor_set(v_reuseFailAlloc_809_, 3, v_a_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_809_, sizeof(void*)*4, v_check_789_);
lean_ctor_set_uint8(v_reuseFailAlloc_809_, sizeof(void*)*4 + 1, v_persistent_790_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_805_);
v___x_807_ = v___x_796_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v___x_816_; 
lean_dec(v_a_794_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v_code_522_);
v___x_816_ = v___x_796_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_code_522_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_522_, 4);
return v___x_793_;
}
}
case 13:
{
lean_object* v_fvarId_819_; lean_object* v_k_820_; lean_object* v___x_821_; 
v_fvarId_819_ = lean_ctor_get(v_code_522_, 0);
v_k_820_ = lean_ctor_get(v_code_522_, 1);
lean_inc_ref(v_k_820_);
v___x_821_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_820_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_844_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_844_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_844_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_844_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
size_t v___x_826_; size_t v___x_827_; uint8_t v___x_828_; 
v___x_826_ = lean_ptr_addr(v_k_820_);
v___x_827_ = lean_ptr_addr(v_a_822_);
v___x_828_ = lean_usize_dec_eq(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_838_; 
lean_inc(v_fvarId_819_);
v_isSharedCheck_838_ = !lean_is_exclusive(v_code_522_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; lean_object* v_unused_840_; 
v_unused_839_ = lean_ctor_get(v_code_522_, 1);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_code_522_, 0);
lean_dec(v_unused_840_);
v___x_830_ = v_code_522_;
v_isShared_831_ = v_isSharedCheck_838_;
goto v_resetjp_829_;
}
else
{
lean_dec(v_code_522_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_838_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v_a_822_);
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_fvarId_819_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_a_822_);
v___x_833_ = v_reuseFailAlloc_837_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_833_);
v___x_835_ = v___x_824_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v___x_842_; 
lean_dec(v_a_822_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_code_522_);
v___x_842_ = v___x_824_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_code_522_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_522_, 2);
return v___x_821_;
}
}
default: 
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v_code_522_);
return v___x_845_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_522_ = stack[0].m_obj;
lean_object* v_a_523_ = stack[1].m_obj;
lean_object* v_a_524_ = stack[2].m_obj;
lean_object* v_a_525_ = stack[3].m_obj;
lean_object* v_a_526_ = stack[4].m_obj;
lean_object* v_res_846_;
v_res_846_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_code_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
stack->m_obj
 = v_res_846_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed(lean_object* v_code_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_code_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_853_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(lean_object* v_i_854_, lean_object* v_as_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_861_ = lean_array_get_size(v_as_855_);
v___x_862_ = lean_nat_dec_lt(v_i_854_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
lean_dec(v_i_854_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v_as_855_);
return v___x_863_;
}
else
{
lean_object* v___f_864_; lean_object* v_a_865_; lean_object* v___x_866_; 
v___f_864_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed), 6, 0);
v_a_865_ = lean_array_fget_borrowed(v_as_855_, v_i_854_);
lean_inc(v_a_865_);
v___x_866_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_a_865_, v___f_864_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; size_t v___x_868_; size_t v___x_869_; uint8_t v___x_870_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = lean_ptr_addr(v_a_865_);
v___x_869_ = lean_ptr_addr(v_a_867_);
v___x_870_ = lean_usize_dec_eq(v___x_868_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_add(v_i_854_, v___x_871_);
v___x_873_ = lean_array_fset(v_as_855_, v_i_854_, v_a_867_);
lean_dec(v_i_854_);
v_i_854_ = v___x_872_;
v_as_855_ = v___x_873_;
goto _start;
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v_a_867_);
v___x_875_ = lean_unsigned_to_nat(1u);
v___x_876_ = lean_nat_add(v_i_854_, v___x_875_);
lean_dec(v_i_854_);
v_i_854_ = v___x_876_;
goto _start;
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v_as_855_);
lean_dec(v_i_854_);
v_a_878_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_866_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_866_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_854_ = stack[0].m_obj;
lean_object* v_as_855_ = stack[1].m_obj;
lean_object* v___y_856_ = stack[2].m_obj;
lean_object* v___y_857_ = stack[3].m_obj;
lean_object* v___y_858_ = stack[4].m_obj;
lean_object* v___y_859_ = stack[5].m_obj;
lean_object* v_res_886_;
v_res_886_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v_i_854_, v_as_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
stack->m_obj
 = v_res_886_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1___boxed(lean_object* v_i_887_, lean_object* v_as_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v_i_887_, v_as_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_894_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(lean_object* v_f_895_, lean_object* v_v_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
if (lean_obj_tag(v_v_896_) == 0)
{
lean_object* v_code_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_926_; 
v_code_902_ = lean_ctor_get(v_v_896_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_v_896_);
if (v_isSharedCheck_926_ == 0)
{
v___x_904_ = v_v_896_;
v_isShared_905_ = v_isSharedCheck_926_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_code_902_);
lean_dec(v_v_896_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_926_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; 
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
lean_inc(v___y_898_);
lean_inc_ref(v___y_897_);
v___x_906_ = lean_apply_6(v_f_895_, v_code_902_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, lean_box(0));
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_917_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_917_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v_a_907_);
v___x_912_ = v___x_904_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_916_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_912_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_del_object(v___x_904_);
v_a_918_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_906_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_906_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
else
{
lean_object* v___x_927_; 
lean_dec_ref(v_f_895_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_v_896_);
return v___x_927_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_895_ = stack[0].m_obj;
lean_object* v_v_896_ = stack[1].m_obj;
lean_object* v___y_897_ = stack[2].m_obj;
lean_object* v___y_898_ = stack[3].m_obj;
lean_object* v___y_899_ = stack[4].m_obj;
lean_object* v___y_900_ = stack[5].m_obj;
lean_object* v_res_928_;
v_res_928_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_895_, v_v_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg___boxed(lean_object* v_f_929_, lean_object* v_v_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_929_, v_v_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
return v_res_936_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(uint8_t v_pu_937_, lean_object* v_f_938_, lean_object* v_v_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_938_, v_v_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v___x_945_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_937_ = stack[0].m_num;
lean_object* v_f_938_ = stack[1].m_obj;
lean_object* v_v_939_ = stack[2].m_obj;
lean_object* v___y_940_ = stack[3].m_obj;
lean_object* v___y_941_ = stack[4].m_obj;
lean_object* v___y_942_ = stack[5].m_obj;
lean_object* v___y_943_ = stack[6].m_obj;
lean_object* v_res_946_;
v_res_946_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(v_pu_937_, v_f_938_, v_v_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___boxed(lean_object* v_pu_947_, lean_object* v_f_948_, lean_object* v_v_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
uint8_t v_pu_boxed_955_; lean_object* v_res_956_; 
v_pu_boxed_955_ = lean_unbox(v_pu_947_);
v_res_956_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(v_pu_boxed_955_, v_f_948_, v_v_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_956_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(lean_object* v_decl_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_toSignature_964_; lean_object* v_value_965_; uint8_t v_recursive_966_; lean_object* v_inlineAttr_x3f_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_992_; 
v_toSignature_964_ = lean_ctor_get(v_decl_958_, 0);
v_value_965_ = lean_ctor_get(v_decl_958_, 1);
v_recursive_966_ = lean_ctor_get_uint8(v_decl_958_, sizeof(void*)*3);
v_inlineAttr_x3f_967_ = lean_ctor_get(v_decl_958_, 2);
v_isSharedCheck_992_ = !lean_is_exclusive(v_decl_958_);
if (v_isSharedCheck_992_ == 0)
{
v___x_969_ = v_decl_958_;
v_isShared_970_ = v_isSharedCheck_992_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_inlineAttr_x3f_967_);
lean_inc(v_value_965_);
lean_inc(v_toSignature_964_);
lean_dec(v_decl_958_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_992_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___f_971_; lean_object* v___x_972_; 
v___f_971_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0));
v___x_972_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v___f_971_, v_value_965_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_983_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_983_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_983_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_983_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v_a_973_);
v___x_978_ = v___x_969_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_toSignature_964_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_a_973_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_inlineAttr_x3f_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_982_, sizeof(void*)*3, v_recursive_966_);
v___x_978_ = v_reuseFailAlloc_982_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_978_);
v___x_980_ = v___x_975_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_del_object(v___x_969_);
lean_dec(v_inlineAttr_x3f_967_);
lean_dec_ref(v_toSignature_964_);
v_a_984_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_972_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_972_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_958_ = stack[0].m_obj;
lean_object* v_a_959_ = stack[1].m_obj;
lean_object* v_a_960_ = stack[2].m_obj;
lean_object* v_a_961_ = stack[3].m_obj;
lean_object* v_a_962_ = stack[4].m_obj;
lean_object* v_res_993_;
v_res_993_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(v_decl_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
stack->m_obj
 = v_res_993_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed(lean_object* v_decl_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(v_decl_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
return v_res_1000_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(lean_object* v_as_1001_, size_t v_i_1002_, size_t v_stop_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_usize_dec_eq(v_i_1002_, v_stop_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_array_uget_borrowed(v_as_1001_, v_i_1002_);
if (lean_obj_tag(v___x_1005_) == 2)
{
uint8_t v___x_1006_; 
v___x_1006_ = 1;
return v___x_1006_;
}
else
{
size_t v___x_1007_; size_t v___x_1008_; 
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_add(v_i_1002_, v___x_1007_);
v_i_1002_ = v___x_1008_;
goto _start;
}
}
else
{
uint8_t v___x_1010_; 
v___x_1010_ = 0;
return v___x_1010_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1001_ = stack[0].m_obj;
size_t v_i_1002_ = stack[1].m_num;
size_t v_stop_1003_ = stack[2].m_num;
uint8_t v_res_1011_;
v_res_1011_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_as_1001_, v_i_1002_, v_stop_1003_);
stack->m_num = v_res_1011_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0___boxed(lean_object* v_as_1012_, lean_object* v_i_1013_, lean_object* v_stop_1014_){
_start:
{
size_t v_i_boxed_1015_; size_t v_stop_boxed_1016_; uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_i_boxed_1015_ = lean_unbox_usize(v_i_1013_);
lean_dec(v_i_1013_);
v_stop_boxed_1016_ = lean_unbox_usize(v_stop_1014_);
lean_dec(v_stop_1014_);
v_res_1017_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_as_1012_, v_i_boxed_1015_, v_stop_boxed_1016_);
lean_dec_ref(v_as_1012_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureHasDefault(lean_object* v_alts_1019_){
_start:
{
lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1038_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = lean_array_get_size(v_alts_1019_);
v___x_1038_ = lean_nat_dec_lt(v___x_1025_, v___x_1026_);
if (v___x_1038_ == 0)
{
goto v___jp_1027_;
}
else
{
if (v___x_1038_ == 0)
{
goto v___jp_1027_;
}
else
{
size_t v___x_1039_; size_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = lean_usize_of_nat(v___x_1026_);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_alts_1019_, v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
goto v___jp_1027_;
}
else
{
return v_alts_1019_;
}
}
}
v___jp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___y_1022_);
v___x_1024_ = lean_array_push(v___y_1021_, v___x_1023_);
return v___x_1024_;
}
v___jp_1027_:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_unsigned_to_nat(2u);
v___x_1029_ = lean_nat_dec_lt(v___x_1026_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v_last_1033_; lean_object* v_alts_1034_; 
v___x_1030_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0, &l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
v___x_1031_ = lean_unsigned_to_nat(1u);
v___x_1032_ = lean_nat_sub(v___x_1026_, v___x_1031_);
v_last_1033_ = lean_array_get(v___x_1030_, v_alts_1019_, v___x_1032_);
lean_dec(v___x_1032_);
v_alts_1034_ = lean_array_pop(v_alts_1019_);
switch(lean_obj_tag(v_last_1033_))
{
case 0:
{
lean_object* v_code_1035_; 
v_code_1035_ = lean_ctor_get(v_last_1033_, 2);
lean_inc_ref(v_code_1035_);
lean_dec_ref_known(v_last_1033_, 3);
v___y_1021_ = v_alts_1034_;
v___y_1022_ = v_code_1035_;
goto v___jp_1020_;
}
case 1:
{
lean_object* v_code_1036_; 
v_code_1036_ = lean_ctor_get(v_last_1033_, 1);
lean_inc_ref(v_code_1036_);
lean_dec_ref_known(v_last_1033_, 2);
v___y_1021_ = v_alts_1034_;
v___y_1022_ = v_code_1036_;
goto v___jp_1020_;
}
default: 
{
lean_object* v_code_1037_; 
v_code_1037_ = lean_ctor_get(v_last_1033_, 0);
lean_inc_ref(v_code_1037_);
lean_dec_ref_known(v_last_1033_, 1);
v___y_1021_ = v_alts_1034_;
v___y_1022_ = v_code_1037_;
goto v___jp_1020_;
}
}
}
else
{
return v_alts_1019_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpCase___closed__3(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = ((lean_object*)(l_Lean_Compiler_LCNF_simpCase___closed__2));
v___x_1048_ = 2;
v___x_1049_ = ((lean_object*)(l_Lean_Compiler_LCNF_simpCase___closed__1));
v___x_1050_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1049_, v___x_1048_, v___x_1047_, v___x_1046_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpCase(void){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_obj_once(&l_Lean_Compiler_LCNF_simpCase___closed__3, &l_Lean_Compiler_LCNF_simpCase___closed__3_once, _init_l_Lean_Compiler_LCNF_simpCase___closed__3);
return v___x_1051_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_));
v___x_1123_ = 1;
v___x_1124_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_));
v___x_1125_ = l_Lean_registerTraceClass(v___x_1122_, v___x_1123_, v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1126_;
v_res_1126_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2____boxed(lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
return v_res_1128_;
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
