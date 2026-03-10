// Lean compiler output
// Module: Lean.Elab.WhereFinally
// Imports: public import Lean.Parser.Term
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
static const lean_ctor_object l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedWhereFinallyView_default = (const lean_object*)&l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedWhereFinallyView = (const lean_object*)&l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_WhereFinallyView_none = (const lean_object*)&l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_WhereFinallyView_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_isNone___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_mkWhereFinallyView___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "`where ... finally` does not currently support any named sub-sections `| sectionName => ...`"};
static const lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_mkWhereFinallyView___redArg___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Elab_mkWhereFinallyView___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___closed__1;
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_WhereFinallyView_isNone(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Syntax_isMissing(x_2);
if (x_4 == 0)
{
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_Lean_Syntax_isMissing(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_isNone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_WhereFinallyView_isNone(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_15; 
x_4 = lean_ctor_get(x_1, 0);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_5 = x_1;
x_6 = x_15;
goto block_14;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_2);
x_10 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_9);
x_10 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_11; 
x_11 = lean_apply_2(x_7, lean_box(0), x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkWhereFinallyView___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_mkWhereFinallyView___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_Syntax_isMissing(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_7);
lean_inc_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_mkWhereFinallyView___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_mkWhereFinallyView___redArg___lam__1), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_16 = l_Lean_Syntax_getArg(x_7, x_4);
x_17 = l_Lean_Syntax_getArg(x_16, x_6);
lean_dec(x_16);
x_18 = l_Lean_Syntax_isMissing(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_7);
goto block_15;
}
else
{
if (x_8 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_10);
lean_dec(x_3);
lean_dec_ref(x_2);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(x_1, x_7, x_19);
return x_20;
}
else
{
lean_dec(x_7);
goto block_15;
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_obj_once(&l_Lean_Elab_mkWhereFinallyView___redArg___closed__1, &l_Lean_Elab_mkWhereFinallyView___redArg___closed__1_once, _init_l_Lean_Elab_mkWhereFinallyView___redArg___closed__1);
x_13 = l_Lean_throwErrorAt___redArg(x_1, x_2, x_3, x_12);
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_13, x_10);
return x_14;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_31; 
lean_dec(x_7);
lean_dec_ref(x_2);
x_21 = lean_ctor_get(x_1, 0);
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_1, 1);
lean_dec(x_32);
x_22 = x_1;
x_23 = x_31;
goto block_30;
}
else
{
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_box(0);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_25);
lean_ctor_set(x_22, 0, x_3);
x_26 = x_22;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_25);
x_26 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_27; 
x_27 = lean_apply_2(x_24, lean_box(0), x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_mkWhereFinallyView___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_WhereFinally(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Term(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_WhereFinally(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_WhereFinally(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_WhereFinally(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_WhereFinally(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_WhereFinally(builtin);
}
#ifdef __cplusplus
}
#endif
