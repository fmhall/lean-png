// Lean compiler output
// Module: PngTest
// Imports: public import Init
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
lean_object* lean_get_stdout();
LEAN_EXPORT lean_object* lp_lean_x2dpng_IO_print___at___00IO_println___at___00main_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dpng_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* lp_lean_x2dpng_IO_println___at___00main_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dpng_IO_println___at___00main_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object lp_lean_x2dpng_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lean-png test suite"};
static const lean_object* lp_lean_x2dpng_main___closed__0 = (const lean_object*)&lp_lean_x2dpng_main___closed__0_value;
static const lean_string_object lp_lean_x2dpng_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 55, .m_data = "No tests yet — add test modules and register them here."};
static const lean_object* lp_lean_x2dpng_main___closed__1 = (const lean_object*)&lp_lean_x2dpng_main___closed__1_value;
LEAN_EXPORT lean_object* _lean_main();
LEAN_EXPORT lean_object* lp_lean_x2dpng_main___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dpng_IO_print___at___00IO_println___at___00main_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stdout();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dpng_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lean_x2dpng_IO_print___at___00IO_println___at___00main_spec__0_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dpng_IO_println___at___00main_spec__0(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = lp_lean_x2dpng_IO_print___at___00IO_println___at___00main_spec__0_spec__0(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dpng_IO_println___at___00main_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lean_x2dpng_IO_println___at___00main_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* _lean_main() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(lp_lean_x2dpng_main___closed__0));
x_3 = lp_lean_x2dpng_IO_println___at___00main_spec__0(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_3);
x_4 = ((lean_object*)(lp_lean_x2dpng_main___closed__1));
x_5 = lp_lean_x2dpng_IO_println___at___00main_spec__0(x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dpng_main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = _lean_main();
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dpng_PngTest(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize_runtime_module();

  #if defined(WIN32) || defined(_WIN32)
  #include <windows.h>
  #endif

  int main(int argc, char ** argv) {
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
  #endif
  lean_object* in; lean_object* res;
argv = lean_setup_args(argc, argv);
lean_initialize_runtime_module();
lean_set_panic_messages(false);
res = initialize_lean_x2dpng_PngTest(1 /* builtin */);
lean_set_panic_messages(true);
lean_io_mark_end_initialization();
if (lean_io_result_is_ok(res)) {
lean_dec_ref(res);
lean_init_task_manager();
res = _lean_main();
}
lean_finalize_task_manager();
if (lean_io_result_is_ok(res)) {
  int ret = 0;
  lean_dec_ref(res);
  return ret;
} else {
  lean_io_result_show_error(res);
  lean_dec_ref(res);
  return 1;
}
}
#ifdef __cplusplus
}
#endif
