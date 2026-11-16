/*
 * DunSuite Lite
 * 三页：计时器 / 待机内存 / 进程调优（时间片、核心与中断隔离、首核）。
 * 诊断：-show；-tab 1..3；--tray；其余开关见 README.md。
 */
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Threading;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Controls.Primitives;
using System.Windows.Input;
using System.Windows.Markup;
using System.Windows.Media;
using DunSuiteLite.Scheduling;

public enum PresetScope { Schedule }

public partial class SuiteApp
{
    /* ---------------- Win32 托盘壳 ---------------- */
    [DllImport("user32.dll")] static extern bool RegisterHotKey(IntPtr h, int id, uint mod, uint vk);
    [DllImport("user32.dll")] static extern bool UnregisterHotKey(IntPtr h, int id);
    [DllImport("shell32.dll", CharSet = CharSet.Unicode)] static extern bool Shell_NotifyIconW(int msg, ref NID data);
    [DllImport("shell32.dll", CharSet = CharSet.Unicode)] static extern int ExtractIconExW(string file, int index, out IntPtr large, out IntPtr small, int count);
    [DllImport("user32.dll")] static extern bool GetCursorPos(out POINT pt);
    [DllImport("user32.dll")] static extern bool PostMessage(IntPtr h, uint msg, IntPtr w, IntPtr l);
    [DllImport("user32.dll", CharSet = CharSet.Unicode)] static extern IntPtr FindWindowExW(IntPtr parent, IntPtr after, string cls, string title);
    [DllImport("user32.dll", CharSet = CharSet.Unicode)] static extern IntPtr FindWindowW(string cls, string title);
    [DllImport("user32.dll")] static extern bool DestroyIcon(IntPtr h);
    [DllImport("user32.dll", CharSet = CharSet.Unicode)] static extern ushort RegisterClassEx(ref WNDCLASSEX wc);
    [DllImport("user32.dll", CharSet = CharSet.Unicode)] static extern IntPtr CreateWindowExW(uint ex, string cls, string name, uint style, int x, int y, int w, int h, IntPtr parent, IntPtr menu, IntPtr inst, IntPtr param);
    [DllImport("user32.dll")] static extern IntPtr DefWindowProcW(IntPtr h, uint msg, IntPtr w, IntPtr l);
    [DllImport("user32.dll")] static extern bool GetMessageW(out MSG msg, IntPtr h, uint min, uint max);
    [DllImport("user32.dll")] static extern bool TranslateMessage(ref MSG m);
    [DllImport("user32.dll")] static extern IntPtr DispatchMessageW(ref MSG m);
    [DllImport("user32.dll")] static extern void PostQuitMessage(int code);
    [DllImport("psapi.dll")] static extern bool EmptyWorkingSet(IntPtr h);
    [DllImport("kernel32.dll")] static extern IntPtr GetCurrentProcess();

    delegate IntPtr WndProcDelegate(IntPtr h, uint msg, IntPtr w, IntPtr l);
    static WndProcDelegate wndProcDelegate; // 留引用防 GC

    [StructLayout(LayoutKind.Sequential)] struct POINT { public int X, Y; }
    [StructLayout(LayoutKind.Sequential)] struct MSG { public IntPtr hwnd; public uint message; public IntPtr wParam, lParam; public uint time; public POINT pt; }
    [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Unicode)]
    struct WNDCLASSEX { public uint cbSize; public uint style; public IntPtr lpfnWndProc; public int cbClsExtra, cbWndExtra; public IntPtr hInstance, hIcon, hCursor, hbrBackground; public string lpszMenuName, lpszClassName; public IntPtr hIconSm; }
    [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Unicode)]
    struct NID
    {
        public int cbSize; public IntPtr hWnd; public int uID, uFlags, uCallbackMessage; public IntPtr hIcon;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 128)] public string szTip;
        public int dwState, dwStateMask, uVersion;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 256)] public string szInfo;
        public int uTimeoutOrVersion;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 64)] public string szInfoTitle;
        public int dwInfoFlags; public Guid guidItem; public IntPtr hBalloonIcon;
    }

    const uint WM_TRAY = 0x0400 + 1, WM_LBUTTONDBLCLK = 0x0203, WM_RBUTTONUP = 0x0205;
    const uint WM_COMMAND = 0x0111, WM_HOTKEY = 0x0312;
    const int HOTKEY_ID = 1;
    const int NIM_ADD = 0, NIM_MODIFY = 1, NIM_DELETE = 2, NIF_MESSAGE = 1, NIF_ICON = 2, NIF_TIP = 4;
    const int MI_OPEN = 1001, MI_PURGE = 1002, MI_EXIT = 1003;

    /* ---------------- 状态 ---------------- */
    Window win;                  // null = 界面未打开（销毁态）
    IntPtr msgHwnd, trayIcon;
    volatile bool running = true;
    int startTab = -1;   // -1=未指定（默认计时器页）；诊断 -tab N 优先
    System.Windows.Threading.Dispatcher uiDisp;   // 主线程 Dispatcher（窗口销毁后仍可用，回调里判 win==null）

    static Mutex singleMtx;

    /* ---- 计时器模块（引擎无窗口常驻，UI 引用随窗口销毁置空） ---- */
    readonly Engine _engine = new Engine();
    AutoTuner _tuner;
    readonly DpcEngine _dpc = new DpcEngine();
    DpcGraph _graph;                               // 跨窗口复用，关窗时从宿主摘下
    System.Windows.Threading.DispatcherTimer _dpcTimer;
    Thread _monThread;
    volatile bool _monRun = true;
    volatile bool _monPause = true;                // 窗口未开=暂停监测
    readonly ManualResetEventSlim _monWake = new ManualResetEventSlim(false);    // 监测唤醒：关窗 Reset 纯阻塞零唤醒
    uint shellHookMsg;                           // RegisterWindowMessage("SHELLHOOK") 动态消息号
    uint taskbarCreatedMsg;                      // RegisterWindowMessage("TaskbarCreated")：Explorer 重启广播
    System.Threading.Timer _trayRetryTimer;      // NIM_ADD 失败重试（开机早于 Explorer 就绪）
    int _trayRetryLeft;
    static readonly int _selfPid = Process.GetCurrentProcess().Id;

    void MonPause() { _monWake.Reset(); _monPause = true; }    // 先清事件再置位：杜绝事件残留导致空转
    void MonResume() { _monWarm = 3; _monPause = false; _monWake.Set(); }   // 预暖3拍：关窗收缩(EmptyWorkingSet)后首批采样缺页/随机落核失真（其他测试机实测"开窗首测1.2"即此伪影），丢弃不上屏
    volatile int _monWarm;                     // 恢复后剩余预暖拍数（仅监测线程递减）
    readonly GameLoad _gameLoad = new GameLoad();
    bool _presetBannerPending;                     // 无窗口时应用了预设，开窗补 banner
    TextBlock lblVal, lblRes, lblSlept, lblStatus, bannerText, lblDpcAvg, lblDpcMax, lblDpcMin, lblDpcState;
    Button btnStart, btnStop, btnTimerMode;
    StackPanel timerAutoPanel, timerManualPanel;
    TextBox tbTimerManual;
    bool timerManualMode;
    System.Windows.Shapes.Path autoCheck;   // 菜单「开机自启」的对勾
    ProgressBar pb;
    Border banner;
    Grid dpcGraphHost;

    /* ---- 待机内存模块 ---- */
    string memMode = "smart";   // off / smart / timer（原 event 模式已删——太弱；standby 改名 smart=智能清理）
    int thresholdMB = 1024, intervalMin = 30;
    bool hotkeyEnabled;
    System.Threading.Timer memTickTimer;
    string lastPurgeMsg = "";
    System.Windows.Threading.DispatcherTimer memLiveTimer;
    TextBlock standbyNum, memInfo, memRatioText, lblLastPurge;
    Border memRatioBar, pillOff, pillSmart, pillTimer, tglHotkey;
    System.Windows.Shapes.Ellipse knobHotkey;
    TextBox tbThreshold, tbInterval;

    /* ---- 时间片模块 ---- */
    ListBox procList;
    TextBox tbSearch;
    ComboBox cbFilter;
    TextBlock lblSliceMsg;
    TextBox tbW32Sep;
    System.Windows.Threading.DispatcherTimer searchDebounce;
    bool _populating;
    bool _syncCb;   // 同名行下拉同步中：挡 SelectionChanged 递归（09-11 六控件同步）
    readonly HashSet<string> _expanded = new HashSet<string>(StringComparer.OrdinalIgnoreCase);   // 同名组展开状态（名字级；刷新保持）

    /* ---- 核心隔离模块（UI 引用随窗口销毁置空） ---- */
    TextBlock lblIsoState;
    StackPanel isoCcdHost;
    StackPanel isoCoreHost;   // 核心格子行容器（硬=CCD 行 / 软=区切换按钮+CCD 行；模式切换只重建这里，中断区不动）
    StackPanel isoModeHost;   // 模式切换 chips（硬隔离/软隔离）
    readonly List<Border> _isoBoxes = new List<Border>();   // 硬隔离区格子，与 Topo.Cores 索引对齐
    readonly List<Border> _softBoxes = new List<Border>();  // 软隔离当前编辑区格子（前台区/隔离区共用一份，切区重建）
    TextBlock _softZoneTabGame, _softZoneTabIso;   // 软隔离区切换文字 tab（09-11 用户：方块按钮与核心格子雷同，改文字 tab）
    int _softEditZone;        // 0=编辑前台区 1=编辑隔离区（CCD 排版不变，双 CCD 不超宽）
    ComboBox _isoModeCombo;   // 模式切换下拉（硬隔离/软隔离；09-11 用户：chips 与核心格子雷同，改下拉）
    readonly List<Border> _irqChips = new List<Border>();   // 中断芯片，Tag=IrqIso.Dev
    Border _irqMaskBtn;                                     // 中断落点「核心」按钮（小窗改模式后回写文字）
    Action<string> _isoStatusHandler;

    // ==== STEP5: 配置/自启/替代旧版整合 ====

    /* ---------------- XAML ---------------- */
    const string XAML = @"
<Window xmlns='http://schemas.microsoft.com/winfx/2006/xaml/presentation'
        xmlns:x='http://schemas.microsoft.com/winfx/2006/xaml'
        Width='660' Height='540' WindowStyle='None' ResizeMode='NoResize'
        AllowsTransparency='True' Background='Transparent'
        WindowStartupLocation='CenterScreen' ShowActivated='False'
        FontFamily='Microsoft YaHei UI' Title='DunSuite Lite'>
  <Window.Resources>
    <LinearGradientBrush x:Key='BgGrad' StartPoint='0,0' EndPoint='1,1'>
      <GradientStop Color='#FAFAFA' Offset='0'/>
      <GradientStop Color='#FFFFFF' Offset='0.55'/>
      <GradientStop Color='#FAFAFA' Offset='1'/>
    </LinearGradientBrush>

    <!-- 卡片双边缘玻璃光：顶部微亮横线 + 底部微暗横线（克制，单色体系内提质感；不用 DropShadowEffect，AllowsTransparency 下有坑） -->
    <LinearGradientBrush x:Key='CardTopGlow' StartPoint='0,0' EndPoint='1,0'>
      <GradientStop Color='#00000000' Offset='0'/>
      <GradientStop Color='#14111111' Offset='0.5'/>
      <GradientStop Color='#00000000' Offset='1'/>
    </LinearGradientBrush>
    <LinearGradientBrush x:Key='CardBottomShade' StartPoint='0,0' EndPoint='1,0'>
      <GradientStop Color='#00000000' Offset='0'/>
      <GradientStop Color='#10111111' Offset='0.5'/>
      <GradientStop Color='#00000000' Offset='1'/>
    </LinearGradientBrush>

    <Style TargetType='Button' x:Key='Btn'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='Background' Value='#FFFFFF'/>
      <Setter Property='Foreground' Value='#111111'/>
      <Setter Property='BorderBrush' Value='#D0D0D0'/>
      <Setter Property='BorderThickness' Value='1'/>
      <Setter Property='Padding' Value='14,7'/>
      <Setter Property='FontSize' Value='12'/>
      <Setter Property='Cursor' Value='Hand'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='Button'>
            <Border Background='{TemplateBinding Background}' BorderBrush='{TemplateBinding BorderBrush}'
                    BorderThickness='{TemplateBinding BorderThickness}' Padding='{TemplateBinding Padding}'
                    CornerRadius='6'>
              <ContentPresenter HorizontalAlignment='Center' VerticalAlignment='Center'/>
            </Border>
            <ControlTemplate.Triggers>
              <Trigger Property='IsMouseOver' Value='True'><Setter Property='Background' Value='#E3E3E3'/></Trigger>
              <Trigger Property='IsEnabled' Value='False'>
                <Setter Property='Foreground' Value='#888888'/><Setter Property='Background' Value='#F3F3F3'/>
              </Trigger>
            </ControlTemplate.Triggers>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>

    <Style TargetType='Button' x:Key='BtnPrimary'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='Background' Value='#111111'/>
      <Setter Property='Foreground' Value='#FFFFFF'/>
      <Setter Property='BorderThickness' Value='0'/>
      <Setter Property='Padding' Value='14,7'/>
      <Setter Property='FontSize' Value='12'/>
      <Setter Property='FontWeight' Value='SemiBold'/>
      <Setter Property='Cursor' Value='Hand'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='Button'>
            <Border Background='{TemplateBinding Background}' Padding='{TemplateBinding Padding}' CornerRadius='6'>
              <ContentPresenter HorizontalAlignment='Center' VerticalAlignment='Center'/>
            </Border>
            <ControlTemplate.Triggers>
              <Trigger Property='IsMouseOver' Value='True'><Setter Property='Background' Value='#111111'/></Trigger>
              <Trigger Property='IsEnabled' Value='False'>
                <Setter Property='Foreground' Value='#666666'/><Setter Property='Background' Value='#888888'/>
              </Trigger>
            </ControlTemplate.Triggers>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>

    <Style TargetType='Button' x:Key='BtnGhost'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='Background' Value='Transparent'/>
      <Setter Property='Foreground' Value='#666666'/>
      <Setter Property='BorderBrush' Value='#D0D0D0'/>
      <Setter Property='BorderThickness' Value='1'/>
      <Setter Property='Padding' Value='14,6'/>
      <Setter Property='FontSize' Value='11'/>
      <Setter Property='Cursor' Value='Hand'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='Button'>
            <Border Background='{TemplateBinding Background}' BorderBrush='{TemplateBinding BorderBrush}'
                    BorderThickness='{TemplateBinding BorderThickness}' Padding='{TemplateBinding Padding}'
                    CornerRadius='6'>
              <ContentPresenter HorizontalAlignment='Center' VerticalAlignment='Center'/>
            </Border>
            <ControlTemplate.Triggers>
              <Trigger Property='IsMouseOver' Value='True'>
                <Setter Property='BorderBrush' Value='#888888'/><Setter Property='Foreground' Value='#333333'/>
              </Trigger>
            </ControlTemplate.Triggers>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>

    <Style TargetType='Button' x:Key='PresetItem'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='Background' Value='Transparent'/>
      <Setter Property='BorderThickness' Value='0'/>
      <Setter Property='Padding' Value='9,7'/>
      <Setter Property='Cursor' Value='Hand'/>
      <Setter Property='HorizontalContentAlignment' Value='Stretch'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='Button'>
            <Border Background='{TemplateBinding Background}' Padding='{TemplateBinding Padding}' CornerRadius='6'>
              <ContentPresenter HorizontalAlignment='Stretch' VerticalAlignment='Center'/>
            </Border>
            <ControlTemplate.Triggers>
              <Trigger Property='IsMouseOver' Value='True'><Setter Property='Background' Value='#F3F3F3'/></Trigger>
            </ControlTemplate.Triggers>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>

    <Style TargetType='Button' x:Key='TitleBtn'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='Background' Value='Transparent'/>
      <Setter Property='Foreground' Value='#666666'/>
      <Setter Property='BorderThickness' Value='0'/>
      <Setter Property='Padding' Value='9,3'/>
      <Setter Property='FontSize' Value='12'/>
      <Setter Property='Cursor' Value='Hand'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='Button'>
            <Border Background='{TemplateBinding Background}' Padding='{TemplateBinding Padding}' CornerRadius='5'>
              <ContentPresenter HorizontalAlignment='Center' VerticalAlignment='Center'/>
            </Border>
            <ControlTemplate.Triggers>
              <Trigger Property='IsMouseOver' Value='True'><Setter Property='Background' Value='#E3E3E3'/></Trigger>
            </ControlTemplate.Triggers>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>

    <Style x:Key='DarkBox' TargetType='TextBox'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='Background' Value='#FAFAFA'/>
      <Setter Property='Foreground' Value='#111111'/>
      <Setter Property='BorderBrush' Value='#D0D0D0'/>
      <Setter Property='FontSize' Value='11'/>
      <Setter Property='Padding' Value='8,4'/>
      <Setter Property='CaretBrush' Value='#111111'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='TextBox'>
            <Border Background='{TemplateBinding Background}' BorderBrush='{TemplateBinding BorderBrush}'
                    BorderThickness='1' CornerRadius='5'>
              <ScrollViewer x:Name='PART_ContentHost' Margin='1,0' VerticalAlignment='Center'/>
            </Border>
            <ControlTemplate.Triggers>
              <Trigger Property='IsFocused' Value='True'><Setter Property='BorderBrush' Value='#888888'/></Trigger>
            </ControlTemplate.Triggers>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>

    <Style x:Key='SliceComboItem' TargetType='ComboBoxItem'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='Foreground' Value='#333333'/>
      <Setter Property='FontSize' Value='11'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='ComboBoxItem'>
            <Border x:Name='bd' Background='Transparent' Padding='8,4' CornerRadius='4' Margin='2,1'>
              <ContentPresenter VerticalAlignment='Center'/>
            </Border>
            <ControlTemplate.Triggers>
              <Trigger Property='IsHighlighted' Value='True'>
                <Setter TargetName='bd' Property='Background' Value='#E3E3E3'/>
                <Setter Property='Foreground' Value='#111111'/>
              </Trigger>
            </ControlTemplate.Triggers>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>

    <Style x:Key='SliceCombo' TargetType='ComboBox'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='Background' Value='#FAFAFA'/>
      <Setter Property='Foreground' Value='#111111'/>
      <Setter Property='BorderBrush' Value='#D0D0D0'/>
      <Setter Property='FontSize' Value='11'/>
      <Setter Property='ItemContainerStyle' Value='{StaticResource SliceComboItem}'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='ComboBox'>
            <Grid>
              <ToggleButton x:Name='PART_Toggle' Focusable='False' ClickMode='Press'
                            IsChecked='{Binding IsDropDownOpen, Mode=TwoWay, RelativeSource={RelativeSource TemplatedParent}}'
                            Background='{TemplateBinding Background}' BorderBrush='{TemplateBinding BorderBrush}'
                            Foreground='{TemplateBinding Foreground}'
                            Content='{TemplateBinding SelectionBoxItem}'>
                <ToggleButton.Template>
                  <ControlTemplate TargetType='ToggleButton'>
                    <Border x:Name='bd' Background='{TemplateBinding Background}' BorderBrush='{TemplateBinding BorderBrush}'
                            BorderThickness='1' CornerRadius='5' Padding='8,3'>
                      <Grid>
                        <ContentPresenter Content='{TemplateBinding Content}' VerticalAlignment='Center' Margin='0,0,12,0'/>
                        <Path Data='M0,0 L4,4 L8,0 Z' Fill='#666666' HorizontalAlignment='Right' VerticalAlignment='Center'/>
                      </Grid>
                    </Border>
                    <ControlTemplate.Triggers>
                      <Trigger Property='IsMouseOver' Value='True'><Setter TargetName='bd' Property='BorderBrush' Value='#888888'/></Trigger>
                      <Trigger Property='IsChecked' Value='True'><Setter TargetName='bd' Property='BorderBrush' Value='#888888'/></Trigger>
                    </ControlTemplate.Triggers>
                  </ControlTemplate>
                </ToggleButton.Template>
              </ToggleButton>
              <Popup x:Name='PART_Popup' Placement='Bottom' AllowsTransparency='True' Focusable='False'
                     IsOpen='{TemplateBinding IsDropDownOpen}' PopupAnimation='None'>   <!-- 禁 Slide：PopupAnimation 走 AnimationClock，本机会顶掉计时器效力 -->
                <Border Background='#FFFFFF' BorderBrush='#D0D0D0' BorderThickness='1' CornerRadius='6'
                        Margin='0,2,0,0' MinWidth='{Binding ActualWidth, RelativeSource={RelativeSource TemplatedParent}}'>
                  <ScrollViewer MaxHeight='220' CanContentScroll='False'>
                    <ItemsPresenter/>
                  </ScrollViewer>
                </Border>
              </Popup>
            </Grid>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>

    <Style TargetType='ScrollBar'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='Width' Value='8'/>
      <Setter Property='Background' Value='Transparent'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='ScrollBar'>
            <Grid Background='Transparent'>
              <Track x:Name='PART_Track' IsDirectionReversed='True' IsEnabled='{TemplateBinding IsMouseOver}'>
                <Track.Thumb>
                  <Thumb>
                    <Thumb.Template>
                      <ControlTemplate TargetType='Thumb'>
                        <Border Background='#D0D0D0' CornerRadius='4' Margin='2,0'/>
                      </ControlTemplate>
                    </Thumb.Template>
                  </Thumb>
                </Track.Thumb>
              </Track>
            </Grid>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>

    <Style x:Key='ProcList' TargetType='ListBox'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='Background' Value='Transparent'/>
      <Setter Property='BorderThickness' Value='0'/>
      <Setter Property='ScrollViewer.HorizontalScrollBarVisibility' Value='Disabled'/>
      <Setter Property='ScrollViewer.VerticalScrollBarVisibility' Value='Auto'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='ListBox'>
            <Border Background='#FFFFFF' BorderBrush='#E3E3E3' BorderThickness='1' CornerRadius='8'>
              <Grid>
                <Border VerticalAlignment='Top' Height='1' Margin='8,0' Background='{StaticResource CardTopGlow}'/>
                <Border VerticalAlignment='Bottom' Height='1' Margin='8,0' Background='{StaticResource CardBottomShade}'/>
                <ScrollViewer Focusable='False' Margin='4'><ItemsPresenter/></ScrollViewer>
              </Grid>
            </Border>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>

    <Style x:Key='ProcItem' TargetType='ListBoxItem'>
      <Setter Property='FocusVisualStyle' Value='{x:Null}'/>
      <Setter Property='HorizontalContentAlignment' Value='Stretch'/>
      <Setter Property='Padding' Value='0'/>
      <Setter Property='Template'>
        <Setter.Value>
          <ControlTemplate TargetType='ListBoxItem'>
            <Border x:Name='bd' Background='Transparent' CornerRadius='5' Margin='0,1' Padding='8,5'>
              <ContentPresenter HorizontalAlignment='Stretch'/>
            </Border>
            <ControlTemplate.Triggers>
              <Trigger Property='IsMouseOver' Value='True'><Setter TargetName='bd' Property='Background' Value='#FFFFFF'/></Trigger>
            </ControlTemplate.Triggers>
          </ControlTemplate>
        </Setter.Value>
      </Setter>
    </Style>
  </Window.Resources>

  <Border BorderBrush='#E3E3E3' BorderThickness='1' CornerRadius='12'
          Background='{StaticResource BgGrad}' ClipToBounds='True'>
    <Grid>
      <Grid.RowDefinitions>
        <RowDefinition Height='40'/><RowDefinition Height='37'/><RowDefinition Height='*'/>
      </Grid.RowDefinitions>

      <!-- 标题栏 -->
      <Border Grid.Row='0' Name='titleBar' Background='Transparent'>
        <Grid>
          <StackPanel Orientation='Horizontal' VerticalAlignment='Center' Margin='16,0,0,0'>
            <TextBlock Text='◆' Foreground='#888888' FontSize='12' VerticalAlignment='Center' Margin='0,0,7,0'/>
            <TextBlock Text='DunSuite Lite' Foreground='#111111' FontSize='13' FontWeight='SemiBold' VerticalAlignment='Center'/>
          </StackPanel>
          <StackPanel Orientation='Horizontal' HorizontalAlignment='Right' VerticalAlignment='Center' Margin='0,0,8,0'>
            <Button Name='btnPreset' Style='{StaticResource TitleBtn}' ToolTip='菜单：预设档案 / 开机自启'>
              <Grid Width='12' Height='12'>
                <Path Stroke='#888888' StrokeThickness='1.3' Data='M1.6,3.2 L10.4,3.2 M1.6,6 L10.4,6 M1.6,8.8 L10.4,8.8'/>
              </Grid>
            </Button>
            <Button Name='btnMin' Style='{StaticResource TitleBtn}' Content='—'/>
            <Button Name='btnClose' Style='{StaticResource TitleBtn}' Content='✕'/>
          </StackPanel>
        </Grid>
      </Border>

      <!-- Tab 条 -->
      <Border Grid.Row='1' BorderBrush='#E3E3E3' BorderThickness='0,0,0,1' Background='Transparent'>
        <Grid Name='tabStrip'>
          <StackPanel Orientation='Horizontal' Margin='10,0,0,0'>
            <Border Name='tabTimer' Padding='14,0' Cursor='Hand' Background='Transparent'>
              <TextBlock Name='tabTimerText' Text='计 时 器' FontSize='12' Foreground='#111111'
                         VerticalAlignment='Center' HorizontalAlignment='Center' Margin='0,0,0,3'/>
            </Border>
            <Border Name='tabMem' Padding='14,0' Cursor='Hand' Background='Transparent'>
              <TextBlock Name='tabMemText' Text='内 存' FontSize='12' Foreground='#888888'
                         VerticalAlignment='Center' HorizontalAlignment='Center' Margin='0,0,0,3'/>
            </Border>
            <Border Name='tabSlice' Padding='14,0' Cursor='Hand' Background='Transparent'>
              <TextBlock Name='tabSliceText' Text='进 程 调 优' FontSize='12' Foreground='#888888'
                         VerticalAlignment='Center' HorizontalAlignment='Center' Margin='0,0,0,3'/>
            </Border>
          </StackPanel>
          <!-- 滑动指示条：三指示条合并为单条，切页时 DispatcherTimer 手动帧平移（禁 AnimationClock 铁律） -->
          <Border Name='tabInd' Height='2' Width='22' Background='#111111' CornerRadius='1'
                  VerticalAlignment='Bottom' HorizontalAlignment='Left'/>
        </Grid>
      </Border>

      <!-- 内容区 -->
      <Grid Grid.Row='2'>

        <!-- ========== 页1 计时器 ========== -->
        <Grid Name='pageTimer' Margin='14,12,14,12'>
          <Grid.RowDefinitions>
            <RowDefinition Height='66'/>
            <RowDefinition Height='22'/>
            <RowDefinition Height='10'/>
            <RowDefinition Height='42'/>
            <RowDefinition Height='Auto'/>
            <RowDefinition Height='*'/>
          </Grid.RowDefinitions>

          <UniformGrid Grid.Row='0' Columns='3'>
            <Border Background='#FFFFFF' BorderBrush='#E3E3E3' BorderThickness='1' CornerRadius='7' Margin='0,0,5,0'>
              <Grid>
                <Border VerticalAlignment='Top' Height='1' Margin='6,0' Background='{StaticResource CardTopGlow}'/>
                <Border VerticalAlignment='Bottom' Height='1' Margin='6,0' Background='{StaticResource CardBottomShade}'/>
                <StackPanel Margin='12,7'>
                  <TextBlock Text='设定值（100ns 单位）' Foreground='#888888' FontSize='10'/>
                  <TextBlock Name='lblVal' Text='—' Foreground='#111111' FontSize='19' FontFamily='Consolas' Margin='0,2,0,0'/>
                </StackPanel>
              </Grid>
            </Border>
            <Border Background='#FFFFFF' BorderBrush='#E3E3E3' BorderThickness='1' CornerRadius='7' Margin='5,0'>
              <Grid>
                <Border VerticalAlignment='Top' Height='1' Margin='6,0' Background='{StaticResource CardTopGlow}'/>
                <Border VerticalAlignment='Bottom' Height='1' Margin='6,0' Background='{StaticResource CardBottomShade}'/>
                <StackPanel Margin='12,7'>
                  <TextBlock Text='实际 RESOLUTION' Foreground='#888888' FontSize='10'/>
                  <TextBlock Name='lblRes' Text='—' Foreground='#111111' FontSize='19' FontFamily='Consolas' Margin='0,2,0,0'/>
                </StackPanel>
              </Grid>
            </Border>
            <Border Background='#FFFFFF' BorderBrush='#E3E3E3' BorderThickness='1' CornerRadius='7' Margin='5,0,0,0'>
              <Grid>
                <Border VerticalAlignment='Top' Height='1' Margin='6,0' Background='{StaticResource CardTopGlow}'/>
                <Border VerticalAlignment='Bottom' Height='1' Margin='6,0' Background='{StaticResource CardBottomShade}'/>
                <StackPanel Margin='12,7'>
                  <TextBlock Text='SLEEP(1) 实测' Foreground='#888888' FontSize='10'/>
                  <TextBlock Name='lblSlept' Text='—' Foreground='#111111' FontSize='19' FontFamily='Consolas' Margin='0,2,0,0'/>
                </StackPanel>
              </Grid>
            </Border>
          </UniformGrid>

          <Grid Grid.Row='1' Margin='2,2,2,0'>
            <TextBlock Name='lblStatus' Text='就绪' Foreground='#666666' FontSize='12' VerticalAlignment='Center'/>
          </Grid>

          <ProgressBar Grid.Row='2' Name='pb' Minimum='0' Maximum='15' Value='0' Height='4'
                       Background='#E3E3E3' Foreground='#111111' BorderThickness='0'/>

          <Grid Grid.Row='3' Margin='0,8,0,0'>
            <StackPanel Orientation='Horizontal' HorizontalAlignment='Left' VerticalAlignment='Center'>
              <StackPanel Name='timerAutoPanel' Orientation='Horizontal'>
                <Button Name='btnStart' Style='{StaticResource Btn}' Content='开始自动测试' Padding='22,8'/>
                <Button Name='btnStop' Style='{StaticResource Btn}' Content='停止' IsEnabled='False' Margin='8,0,0,0' Padding='22,8'/>
              </StackPanel>
              <StackPanel Name='timerManualPanel' Orientation='Horizontal' Visibility='Collapsed'>
                <TextBox Name='tbTimerManual' Style='{StaticResource DarkBox}' Width='78' MaxLength='10'
                         FontFamily='Consolas' HorizontalContentAlignment='Center' VerticalAlignment='Center'
                         ToolTip='输入计时器设定值（100ns 单位），例如 5000 ≈ 0.5ms'/>
                <Button Name='btnManualApply' Style='{StaticResource Btn}' Content='应用设定' Padding='14,8' Margin='8,0,0,0'/>
              </StackPanel>
              <Button Name='btnTimerMode' Style='{StaticResource BtnGhost}' Content='手动输入' Padding='10,7' Margin='8,0,0,0'
                      VerticalAlignment='Center' ToolTip='切换到手动输入设定值'/>
            </StackPanel>
          </Grid>

          <Border Grid.Row='4' Name='banner' Visibility='Collapsed' Background='#FFFFFF' BorderBrush='#D0D0D0'
                  BorderThickness='1' CornerRadius='7' Padding='12,8' Margin='0,8,0,0'>
            <TextBlock Name='bannerText' Foreground='#111111' FontSize='12.5' FontWeight='SemiBold' TextWrapping='Wrap'/>
          </Border>

          <Border Grid.Row='5' Background='#FFFFFF' BorderBrush='#E3E3E3' BorderThickness='1' CornerRadius='8'
                  Margin='0,10,0,0'>
            <Grid>
              <Border VerticalAlignment='Top' Height='1' Margin='8,0' Background='{StaticResource CardTopGlow}'/>
              <Border VerticalAlignment='Bottom' Height='1' Margin='8,0' Background='{StaticResource CardBottomShade}'/>
              <Grid Margin='10,8'>
                <Grid.RowDefinitions>
                  <RowDefinition Height='18'/>
                  <RowDefinition Height='44'/>
                  <RowDefinition Height='*'/>
                </Grid.RowDefinitions>
                <Grid Grid.Row='0'>
                  <TextBlock Text='DPC 延迟（内核驱动直读）' Foreground='#888888' FontSize='10' VerticalAlignment='Center'/>
                  <TextBlock Name='lblDpcState' Text='' Foreground='#888888' FontSize='10' HorizontalAlignment='Right' VerticalAlignment='Center'/>
                </Grid>
                <UniformGrid Grid.Row='1' Columns='3' Margin='0,3,0,3'>
                  <StackPanel Margin='0,0,8,0'>
                    <TextBlock Text='当前 AVG' Foreground='#888888' FontSize='9'/>
                    <TextBlock Name='lblDpcAvg' Text='—' Foreground='#111111' FontSize='16' FontFamily='Consolas'/>
                  </StackPanel>
                  <StackPanel Margin='4,0'>
                    <TextBlock Text='最大 MAX' Foreground='#888888' FontSize='9'/>
                    <TextBlock Name='lblDpcMax' Text='—' Foreground='#4A4A4A' FontSize='16' FontFamily='Consolas'/>
                  </StackPanel>
                  <StackPanel Margin='8,0,0,0'>
                    <TextBlock Text='最小 MIN' Foreground='#888888' FontSize='9'/>
                    <TextBlock Name='lblDpcMin' Text='—' Foreground='#666666' FontSize='16' FontFamily='Consolas'/>
                  </StackPanel>
                </UniformGrid>
                <Grid Grid.Row='2' Name='dpcGraphHost' MinHeight='84'/>
              </Grid>
            </Grid>
          </Border>
        </Grid>

        <!-- ========== 页2 内存 ========== -->
        <Grid Name='pageMem' Margin='14,12,14,12' Visibility='Collapsed'>
          <Grid.RowDefinitions>
            <RowDefinition Height='150'/>
            <RowDefinition Height='52'/>
            <RowDefinition Height='34'/>
            <RowDefinition Height='34'/>
            <RowDefinition Height='34'/>
            <RowDefinition Height='*'/>
            <RowDefinition Height='22'/>
          </Grid.RowDefinitions>

          <Border Grid.Row='0' Background='#FFFFFF' BorderBrush='#E3E3E3' BorderThickness='1' CornerRadius='10'>
            <Grid>
              <Border VerticalAlignment='Top' Height='1' Margin='9,0' Background='{StaticResource CardTopGlow}'/>
              <Border VerticalAlignment='Bottom' Height='1' Margin='9,0' Background='{StaticResource CardBottomShade}'/>
              <Grid Margin='24,14'>
                <StackPanel VerticalAlignment='Center'>
                  <TextBlock Text='S T A N D B Y   C A C H E' Foreground='#888888' FontSize='10'/>
                  <StackPanel Orientation='Horizontal' Margin='0,4,0,0'>
                    <TextBlock Name='standbyNum' Text='2,048' Foreground='#111111' FontSize='54' FontWeight='Light' FontFamily='Consolas'/>
                    <TextBlock Text=' MB' Foreground='#666666' FontSize='16' VerticalAlignment='Bottom' Margin='6,0,0,13'/>
                  </StackPanel>
                </StackPanel>
                <StackPanel HorizontalAlignment='Right' VerticalAlignment='Center'>
                  <TextBlock Name='memInfo' Text='物理 32.0 GB · 可用 21.4 GB' Foreground='#666666' FontSize='12' HorizontalAlignment='Right'/>
                  <TextBlock Name='memRatioText' Text='待机占物理内存 6%' Foreground='#888888' FontSize='10' HorizontalAlignment='Right' Margin='0,10,0,5'/>
                  <Border Width='180' Height='4' Background='#E3E3E3' CornerRadius='2' HorizontalAlignment='Right'>
                    <Border Name='memRatioBar' Width='11' Height='4' Background='#111111' CornerRadius='2' HorizontalAlignment='Left'/>
                  </Border>
                </StackPanel>
              </Grid>
            </Grid>
          </Border>

          <Grid Grid.Row='1' Margin='0,12,0,0'>
            <Button Name='btnPurge' Style='{StaticResource BtnPrimary}' Content='立 即 清 理' Width='180'
                    HorizontalAlignment='Left' Padding='0,12'/>
            <Button Name='btnRefresh' Style='{StaticResource BtnGhost}' Content='刷 新' Width='110'
                    HorizontalAlignment='Right' Padding='0,10'/>
          </Grid>

          <Grid Grid.Row='2' Margin='2,4,0,0'>
            <TextBlock Text='自动清理' Foreground='#333333' FontSize='12' VerticalAlignment='Center'/>
            <StackPanel Orientation='Horizontal' HorizontalAlignment='Right' VerticalAlignment='Center'>
              <Border x:Name='pillOff' Width='48' Height='22' CornerRadius='11' Cursor='Hand' Margin='4,0,0,0'><TextBlock Text='关闭' FontSize='11' HorizontalAlignment='Center' VerticalAlignment='Center'/></Border>
              <Border x:Name='pillSmart' Width='64' Height='22' CornerRadius='11' Cursor='Hand' Margin='4,0,0,0'><TextBlock Text='智能清理' FontSize='11' HorizontalAlignment='Center' VerticalAlignment='Center'/></Border>
              <Border x:Name='pillTimer' Width='48' Height='22' CornerRadius='11' Cursor='Hand' Margin='4,0,0,0'><TextBlock Text='定时' FontSize='11' HorizontalAlignment='Center' VerticalAlignment='Center'/></Border>
            </StackPanel>
          </Grid>

          <Grid Grid.Row='3' Margin='2,0,0,0'>
            <StackPanel Orientation='Horizontal' VerticalAlignment='Center'>
              <TextBlock Text='待机超' Foreground='#666666' FontSize='11' VerticalAlignment='Center'/>
              <TextBox x:Name='tbThreshold' Style='{StaticResource DarkBox}' Width='56' Text='1024' Margin='4,0'
                       HorizontalContentAlignment='Center' VerticalAlignment='Center'/>
              <TextBlock Text='MB 清 · 每' Foreground='#666666' FontSize='11' VerticalAlignment='Center'/>
              <TextBox x:Name='tbInterval' Style='{StaticResource DarkBox}' Width='44' Text='30' Margin='4,0'
                       HorizontalContentAlignment='Center' VerticalAlignment='Center'/>
              <TextBlock Text='分钟定时清' Foreground='#666666' FontSize='11' VerticalAlignment='Center'/>
            </StackPanel>
          </Grid>

          <Grid Grid.Row='4' Margin='2,0,0,0'>
            <TextBlock Text='全局热键 Ctrl+Shift+M 手动清理' Foreground='#333333' FontSize='12' VerticalAlignment='Center'/>
            <Border x:Name='tglHotkey' Width='38' Height='20' CornerRadius='10' HorizontalAlignment='Right' Cursor='Hand' Background='#E3E3E3' VerticalAlignment='Center'>
              <Ellipse x:Name='knobHotkey' Width='14' Height='14' Fill='#666666' HorizontalAlignment='Left' Margin='3,0'/>
            </Border>
          </Grid>

          <TextBlock Grid.Row='6' Name='lblLastPurge' Text='最近清理：—' Foreground='#888888' FontSize='11'
                     HorizontalAlignment='Center' VerticalAlignment='Center'/>
        </Grid>

        <!-- ========== 页3 时间片 ========== -->
        <Grid Name='pageSlice' Margin='14,12,14,12' Visibility='Collapsed'>
          <Grid.RowDefinitions>
            <RowDefinition Height='Auto'/>
            <RowDefinition Height='32'/>
            <RowDefinition Height='*'/>
            <RowDefinition Height='24'/>
          </Grid.RowDefinitions>

          <!-- 核心隔离区：硬隔离=勾选核心为隔离区（系统/其他进程收拢），不勾=前台区；软隔离=两区独立选核可重叠 -->
          <Border Grid.Row='0' Background='#FFFFFF' BorderBrush='#E3E3E3' BorderThickness='1' CornerRadius='8' Margin='0,0,0,8'>
            <Grid>
              <Border VerticalAlignment='Top' Height='1' Margin='8,0' Background='{StaticResource CardTopGlow}'/>
              <Border VerticalAlignment='Bottom' Height='1' Margin='8,0' Background='{StaticResource CardBottomShade}'/>
              <StackPanel Margin='10,8'>
                <Grid>
                  <StackPanel Orientation='Horizontal' VerticalAlignment='Center'>
                    <TextBlock Text='核 心 隔 离' Foreground='#333333' FontSize='12' VerticalAlignment='Center'/>
                    <StackPanel Name='isoModeHost' Orientation='Horizontal' Margin='14,0,0,0' VerticalAlignment='Center'/>
                  </StackPanel>
                  <TextBlock Name='lblIsoState' Text='' Foreground='#888888' FontSize='10' HorizontalAlignment='Right' VerticalAlignment='Center'/>
                </Grid>
                <StackPanel Name='isoCcdHost'>
                  <StackPanel Name='isoCoreHost'/>
                </StackPanel>
              </StackPanel>
            </Grid>
          </Border>

          <DockPanel Grid.Row='1' Margin='0,0,0,6'>
            <Button Name='btnRefreshProc' DockPanel.Dock='Right' Style='{StaticResource BtnGhost}' Content='刷 新' Width='80'
                    VerticalAlignment='Center' Padding='0,5'/>
            <StackPanel DockPanel.Dock='Right' Orientation='Horizontal' VerticalAlignment='Center' Margin='0,0,14,0'>
              <TextBlock Text='Win32 分离值' Foreground='#666666' FontSize='10' VerticalAlignment='Center' Margin='0,0,6,0'
                         ToolTip='系统线程时间片的分配策略（注册表直写，重启后生效）&#x0a;游戏常用 0x26(38)=长时间片·前台最大提升&#x0a;十进制或 0x 十六进制输入'/>
              <TextBox Name='tbW32Sep' Style='{StaticResource DarkBox}' Width='60' VerticalAlignment='Center' FontFamily='Consolas'/>
              <Button Name='btnW32Sep' Style='{StaticResource BtnGhost}' Content='应用' Width='52' Margin='6,0,0,0' VerticalAlignment='Center' Padding='0,5'/>
            </StackPanel>
            <StackPanel Orientation='Horizontal' VerticalAlignment='Center'>
              <TextBox Name='tbSearch' Style='{StaticResource DarkBox}' Width='170' VerticalAlignment='Center'/>
              <ComboBox Name='cbFilter' Style='{StaticResource SliceCombo}' Width='104' Margin='8,0,0,0' VerticalAlignment='Center'/>
            </StackPanel>
          </DockPanel>

          <ListBox Grid.Row='2' Name='procList' Style='{StaticResource ProcList}' ItemContainerStyle='{StaticResource ProcItem}'/>

          <TextBlock Grid.Row='3' Name='lblSliceMsg' Foreground='#888888' FontSize='10' VerticalAlignment='Center' Margin='2,0,0,0'
                     Text='时间片=进程调度档 · 核心规则=前台/后台分区 · 首核=主线程钉核 · 系统关键进程已隐藏'/>
        </Grid>

      </Grid>

      <!-- 预设下拉菜单（点标题栏 ⇅ 展开；最上层防内容区遮挡） -->
      <Border Name='presetMenu' Visibility='Collapsed' Panel.ZIndex='50'
              Grid.Row='0' Grid.RowSpan='3' HorizontalAlignment='Right' VerticalAlignment='Top' Margin='0,33,10,0'
              Background='#FFFFFF' BorderBrush='#E3E3E3' BorderThickness='1' CornerRadius='9' Padding='4' Opacity='0'>
        <StackPanel Width='168'>
          <TextBlock Text='预 设 档 案' Foreground='#888888' FontSize='9' Margin='9,3,0,4'/>
          <Button Name='pmLoad' Style='{StaticResource PresetItem}'>
            <Grid>
              <TextBlock Text='载入预设' Foreground='#333333' FontSize='11.5' VerticalAlignment='Center'/>
              <TextBlock Text='导入' Foreground='#888888' FontSize='9' HorizontalAlignment='Right' VerticalAlignment='Center'/>
            </Grid>
          </Button>
          <Button Name='pmSave' Style='{StaticResource PresetItem}'>
            <Grid>
              <TextBlock Text='导出预设' Foreground='#333333' FontSize='11.5' VerticalAlignment='Center'/>
              <TextBlock Text='保存' Foreground='#888888' FontSize='9' HorizontalAlignment='Right' VerticalAlignment='Center'/>
            </Grid>
          </Button>
          <Border Height='1' Background='#E3E3E3' Margin='9,3,9,3'/>
          <Button Name='pmAuto' Style='{StaticResource PresetItem}' ToolTip='登录时自动启动 DunSuite Lite（点击切换）'>
            <Grid>
              <TextBlock Text='开机自启' Foreground='#333333' FontSize='11.5' VerticalAlignment='Center'/>
              <Path Name='pmAutoCheck' Stroke='#D0D0D0' StrokeThickness='1.5' StrokeStartLineCap='Round' StrokeEndLineCap='Round'
                    Data='M0.5,4.6 L3.4,7.3 L8.5,1.6' HorizontalAlignment='Right' VerticalAlignment='Center'/>
            </Grid>
          </Button>
        </StackPanel>
      </Border>

      <!-- 轻提示（载入/导出结果，3 秒自动收起） -->
      <Border Name='presetToast' Visibility='Collapsed' Panel.ZIndex='60' Opacity='0'
              Grid.Row='0' Grid.RowSpan='3' HorizontalAlignment='Center' VerticalAlignment='Top' Margin='0,32,0,0'
              Background='#111111' CornerRadius='6' Padding='14,7'>
        <TextBlock Name='presetToastText' Foreground='#FFFFFF' FontSize='11'/>
      </Border>
    </Grid>
  </Border>
</Window>";

    // 无请求全局 Sleep 探针（2026-08-28，22H2 全局效力判据）：本进程不请求任何计时器分辨率，
    // Sleep(1) 实测=无请求进程眼中的全局粒度。（GetTickCount64 在 22H2 恒定 15.6 更新，已证伪不可用作探针；
    // 自身 slept 只反映本进程请求效力，也测不出全局——唯有干净子进程是真判据。）
    // 无窗无消息循环，位于主程序初始化之前。
    static int SleepSampleCli(string outFile)
    {
        long freq; Native.QueryPerformanceFrequency(out freq);
        var v = new double[20];
        for (int k = 0; k < 20; k++)
        {
            long a, b;
            Native.QueryPerformanceCounter(out a);
            Thread.Sleep(1);
            Native.QueryPerformanceCounter(out b);
            v[k] = (b - a) * 1000.0 / freq;
        }
        Array.Sort(v);
        try { File.WriteAllText(outFile, v[10].ToString("F3")); } catch { }
        return 0;
    }

    /* ---------------- 入口 ---------------- */
    [STAThread]
    static int Main(string[] args)
    {
        try
        {
            AppDomain.CurrentDomain.UnhandledException += delegate (object sender, UnhandledExceptionEventArgs e)
            {
                try
                {
                    File.AppendAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_crash.txt"),
                        DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss.fff ") + (e.ExceptionObject != null ? e.ExceptionObject.ToString() : "(null)") + "\r\n\r\n");
                }
                catch { }
            };
            var app = new SuiteApp();
            for (int i = 0; i < args.Length; i++)
                if (args[i] == "-etwraw")
                {
                    string rp = EtwProc.RawProbe();
                    Console.WriteLine(rp);
                    try { File.WriteAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_etwraw.txt"), rp); } catch { }
                    return 0;
                }
            bool trayArg = false, explicitShow = false;
            for (int i = 0; i < args.Length; i++)
            {
                if (args[i] == "--tray") trayArg = true;
                if (args[i] == "-show") explicitShow = true;
                if (args[i] == "-sleepsample" && i + 1 < args.Length) return SleepSampleCli(args[i + 1]);
                if (args[i] == "-selftest") return SelfTest();
                if (args[i] == "-isotopo") return IsoTopoCli();
                if (args[i] == "-isowatch") return IsoWatchCli();
                if (args[i] == "-irqenum") return IrqEnumCli();
                if (args[i] == "-tab" && i + 1 < args.Length) int.TryParse(args[i + 1], out app.startTab);
            }
            bool show = explicitShow || !trayArg;
            bool created;
            singleMtx = new Mutex(true, "Global\\DunSuiteLite_Single", out created);
            if (!created)
            {
                if (show) SignalRunningInstance();
                return 0;
            }
            for (int i = 0; i < args.Length; i++)
            {
                if (args[i] == "-purge") return PurgeStandby(false) ? 0 : 2;
                if (args[i] == "-purgelow") return PurgeStandby(true) ? 0 : 2;
                if (args[i] == "-tsapply" && i + 2 < args.Length) return TsApplyCli(args[i + 1], args[i + 2]);
                if (args[i] == "-isotest" && i + 2 < args.Length) return IsoTestCli(args[i + 1], args[i + 2]);
                if (args[i] == "-isoengage" && i + 1 < args.Length) return IsoEngageCli(args[i + 1]);
                if (args[i] == "-irqset" && i + 2 < args.Length) return IrqSetCli(args[i + 1], args[i + 2]);
                if (args[i] == "-fcapply" && i + 2 < args.Length) return FirstCore.ApplyCli(args[i + 1], args[i + 2]);
            }
            app.Init();
            if (show) app.ShowMain();
            app.MessageLoop();
            return 0;
        }
        catch (Exception ex)
        {
            try { File.WriteAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_crash.txt"), ex.ToString()); } catch { }
            return 1;
        }
    }

    // 第二实例唤出：FindWindowEx(HWND_MESSAGE) 找首实例消息窗，投递"打开主界面"（与托盘菜单同 ID 同路径）
    static void SignalRunningInstance()
    {
        try
        {
            IntPtr h = FindWindowW("DunSuiteLiteMsgCls", null);   // 新版=隐藏顶层窗口
            if (h == IntPtr.Zero) h = FindWindowExW(new IntPtr(-3), IntPtr.Zero, "DunSuiteLiteMsgCls", null);   // 兼容旧版 message-only
            if (h != IntPtr.Zero) PostMessage(h, WM_COMMAND, (IntPtr)MI_OPEN, IntPtr.Zero);
        }
        catch { }
    }

    /* ---------------- 壳初始化：消息窗 + 托盘 ---------------- */
    void Init()
    {
        wndProcDelegate = RawWndProc;
        var wc = new WNDCLASSEX
        {
            cbSize = (uint)Marshal.SizeOf(typeof(WNDCLASSEX)),
            lpfnWndProc = Marshal.GetFunctionPointerForDelegate(wndProcDelegate),
            hInstance = Process.GetCurrentProcess().Handle,
            lpszClassName = "DunSuiteLiteMsgCls"
        };
        RegisterClassEx(ref wc);
        msgHwnd = CreateWindowExW(0, "DunSuiteLiteMsgCls", "DunSuiteLiteMsg", 0, 0, 0, 0, 0, IntPtr.Zero, IntPtr.Zero, IntPtr.Zero, IntPtr.Zero);
        shellHookMsg = Native.RegisterWindowMessage("SHELLHOOK");
        Native.RegisterShellHookWindow(msgHwnd);
        taskbarCreatedMsg = Native.RegisterWindowMessage("TaskbarCreated");

        IntPtr traySmall;
        ExtractIconExW(Process.GetCurrentProcess().MainModule.FileName, 0, out trayIcon, out traySmall, 1);
        if (traySmall != IntPtr.Zero) DestroyIcon(traySmall);
        AddTrayIcon();

        Cfg.Load();
        MigrateAutostartArg();
        Native.SetPriorityClass(Native.GetCurrentProcess(), Native.BelowNormalPriorityClass);
        Task.Run(() => { Thread.Sleep(2000); SelfOptimize(); });
        _tuner = new AutoTuner(_engine, DebugLog, UpdateStats, UpdateProgress, UpdateStatus);
        _tuner.Finished += OnFinished;
        PowerOptOut();
        ApplyPreset();
        if (Cfg.DpcUnlock == 1) { _dpcKeepAlive = true; StartDpc(false); }
        else DpcEngine.CleanupOrphan();
        StartMonitor();

        memMode = Cfg.MemMode; thresholdMB = Cfg.MemThreshold;
        intervalMin = Cfg.MemInterval; hotkeyEnabled = Cfg.MemHotkey;
        new Thread(MemEventLoop) { IsBackground = true }.Start();
        ApplyMemMode();
        ApplyHotkey();

        EnablePrivilege("SeIncreaseBasePriorityPrivilege");
        ApplySliceRulesToRunning();
        Iso.Init();
        FollowIsoSelf();
        FirstCore.Status = SliceMsg;
        FirstCore.Init();

        _startupTrimTimer = new System.Threading.Timer(_ =>
        {
            try { GC.Collect(); GC.WaitForPendingFinalizers(); EmptyWorkingSet(GetCurrentProcess()); } catch { }
        }, null, 5000, Timeout.Infinite);
        _checkTimer = new System.Threading.Timer(_ => TrayTrim(), null, 600000, 600000);
        TimerDog.Notified += s => { if (lblStatus != null) UpdateStatus(s); };
        TimerDog.DriverFallback = () =>
        {
            if (_autoDriver) return false;
            _autoDriver = true;
            return _dpc.Start(Cfg.DpcInterval, Cfg.DpcStreamOff == 1);
        };
    }

    /* ---------------- 托盘图标：失败重试 + Explorer 重启重建 ---------------- */
    NID BuildTrayNid()
    {
        return new NID
        {
            cbSize = Marshal.SizeOf(typeof(NID)),
            hWnd = msgHwnd,
            uID = 1,
            uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP,
            uCallbackMessage = (int)WM_TRAY,
            hIcon = trayIcon,
            szTip = "DunSuiteLite 性能套件"
        };
    }

    void AddTrayIcon()
    {
        try
        {
            var nid = BuildTrayNid();
            if (Shell_NotifyIconW(NIM_ADD, ref nid)) return;
        }
        catch { }
        // 失败起 3s 周期重试，最多 40 次（2 分钟，覆盖慢登录/Explorer 尚未完成初始化）
        if (_trayRetryTimer != null) return;
        _trayRetryLeft = 40;
        _trayRetryTimer = new System.Threading.Timer(_ =>
        {
            try
            {
                var n = BuildTrayNid();
                if (Shell_NotifyIconW(NIM_ADD, ref n) || --_trayRetryLeft <= 0)
                {
                    var t = _trayRetryTimer; _trayRetryTimer = null;
                    if (t != null) t.Dispose();
                }
            }
            catch { }
        }, null, 3000, 3000);
    }

    // 托盘图标存活探测：NIM_MODIFY 空修改失败=图标已丢→重添（第二实例唤出时顺带调用）
    void EnsureTrayAlive()
    {
        try
        {
            var nid = new NID { cbSize = Marshal.SizeOf(typeof(NID)), hWnd = msgHwnd, uID = 1, uFlags = 0 };
            if (!Shell_NotifyIconW(NIM_MODIFY, ref nid)) AddTrayIcon();
        }
        catch { }
    }

    void ApplyPreset()
    {
        if (Cfg.TimerValue == 0) return;
        _engine.Apply(Cfg.TimerValue);   // 同时把守护下限跟随到设定值
        _presetBannerPending = true;
    }

    // 防电源节流标记：声明"不许忽略本进程的计时器请求"（Win10 1809+）
    static void PowerOptOut()
    {
        try
        {
            var s = new Native.PROCESS_POWER_THROTTLING_STATE { Version = 1, ControlMask = 2, StateMask = 0 };
            IntPtr p = Marshal.AllocHGlobal(12);
            Marshal.StructureToPtr(s, p, false);
            Native.SetProcessInformation(Native.GetCurrentProcess(), 4, p, 12);   // ProcessPowerThrottling=4
            Marshal.FreeHGlobal(p);
        }
        catch { }
    }

    System.Threading.Timer _startupTrimTimer, _checkTimer;   // 必须留引用：无引用的 Timer 会被 GC 回收静默失效

    // 托盘期每 10 分钟收缩工作集（CLR/WPF 惰性页面 + 反作弊扫描打回的驻留）
    // 注：30s 实测巡检+异值重求已于 2026-08-16 移除——所有确诊降级均源自自家 WPF AnimationClock
    // 切页动画与 ComboBox Slide 已全部禁用，避免动画时钟干扰计时器。
    // 若未来出现无窗场景的环境降级再考虑加回（Reassert/SampleBurst 仍保留在 Engine 里）。
    void TrayTrim()
    {
        try
        {
            if (win != null) return;   // 窗口开着不折腾
            CheckStandbyThreshold();   // 待机阈值 10min 兜底（挂机期覆盖）
            GC.Collect();
            GC.WaitForPendingFinalizers();
            EmptyWorkingSet(GetCurrentProcess());
        }
        catch { }
    }

    // 自我 ngen 预编译（换路径/换版本自动重做）
    // 2026-10-13 修：stamp 由「路径+LastWriteTime」改「路径+内容 MD5」——payload 下发解压可能保留原时间戳
    // （路径+时间戳不变 → 老标记误判已做 → 内容已变的 exe 永远不重编 → 每次更新后 UI 动画 JIT 卡，用户实测）
    static void SelfOptimize()
    {
        try
        {
            string exePath = Assembly.GetExecutingAssembly().Location;
            string stamp;
            using (var md5 = System.Security.Cryptography.MD5.Create())
            using (var fs = File.OpenRead(exePath))
                stamp = exePath + "|" + BitConverter.ToString(md5.ComputeHash(fs));
            using (var k = Microsoft.Win32.Registry.CurrentUser.OpenSubKey(@"Software\DunSuiteLite"))
            {
                if (k != null && (string)k.GetValue("NgenDone", "") == stamp) return;
            }
            string ngen = Path.Combine(RuntimeEnvironment.GetRuntimeDirectory(), "ngen.exe");
            var p = Process.Start(new ProcessStartInfo
            {
                FileName = ngen,
                Arguments = "install \"" + exePath + "\" /nologo /silent",
                CreateNoWindow = true,
                UseShellExecute = false,
                WindowStyle = ProcessWindowStyle.Hidden
            });
            if (p != null) p.WaitForExit();
            using (var k = Microsoft.Win32.Registry.CurrentUser.CreateSubKey(@"Software\DunSuiteLite"))
                k.SetValue("NgenDone", stamp);
        }
        catch { }
    }

    static int SelfTest()
    {
        string logFile = Path.Combine(Path.GetTempPath(), "dunsuitelite_selftest.txt");
        using (var w = new StreamWriter(logFile, false))
        {
            Action<string> log = s => { w.WriteLine(s); w.Flush(); };
            var engine = new Engine();
            var tuner = new AutoTuner(engine, log, null, null, null);
            var done = new ManualResetEventSlim();
            tuner.Finished += (ok, val, res) => { log(ok ? "SUCCESS" : "FAIL"); done.Set(); };
            tuner.RunAsync();
            done.Wait();
            engine.Release();
        }
        return 0;
    }

    // 时间片命令行诊断：-tsapply <pid> <-1|0-9>（-1=清除 0-9=SchedulingClass）
    // winexe 无控制台，结果写 %TEMP%\dunsuitelite_tsapply.txt
    static int TsApplyCli(string sPid, string sSc)
    {
        int pid, sc;
        string result;
        if (!int.TryParse(sPid, out pid) || !int.TryParse(sSc, out sc))
        {
            result = "usage: -tsapply <pid> <-1|0-9>";
        }
        else
        {
            string r = Slice.ApplyClass(pid, sc);
            bool inJob;
            int cur = Slice.QueryClass(pid, out inJob);
            result = string.Format("apply({0},{1}) -> {2} | query: inOurJob={3} class={4} qerr={5}", pid, sc, r, inJob, cur, Slice.LastQueryError);
        }
        try { File.WriteAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_tsapply.txt"), result); } catch { }
        return result.StartsWith("apply") && (result.Contains("-> OK") || result.Contains("已清除") || result.Contains("忽略")) ? 0 : 2;
    }

    // 核心隔离诊断：-isotopo 拓扑 dump / -isotest <pid> <hexmask> 单进程设定+读回+还原 / -isoengage <name> 全链路演练（生效→取证→还原）
    static int IsoTopoCli()
    {
        Topo.Detect();
        var sb = new System.Text.StringBuilder();
        sb.AppendLine("Supported=" + Topo.Supported + " Logical=" + Topo.LogicalCount + " AllMask=0x" + Topo.AllMask.ToString("X") + " Hybrid=" + Topo.Hybrid);
        for (int c = 0; c < Topo.Ccds.Count; c++)
            sb.AppendLine(Topo.CcdLabel(c) + " mask=0x" + Topo.Ccds[c].Mask.ToString("X"));
        for (int i = 0; i < Topo.Cores.Count; i++)
            sb.AppendLine("core" + i + " mask=0x" + Topo.Cores[i].Mask.ToString("X") + " ccd=" + Topo.Cores[i].Ccd);
        try { File.WriteAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_isotopo.txt"), sb.ToString()); } catch { }
        return 0;
    }

    static int IsoTestCli(string sPid, string sMask)
    {
        int pid; ulong mask;
        string r;
        if (!int.TryParse(sPid, out pid) || !ulong.TryParse(sMask, System.Globalization.NumberStyles.HexNumber, null, out mask))
            r = "usage: -isotest <pid> <hexmask>";
        else
        {
            IntPtr h = Native.OpenProcess(0x200 | 0x1000, false, pid);   // SET_INFORMATION | QUERY_LIMITED
            if (h == IntPtr.Zero) r = "OpenProcess:" + Marshal.GetLastWin32Error();
            else
            {
                UIntPtr orig, sys, back, sys2;
                bool got = Native.GetProcessAffinityMask(h, out orig, out sys);
                bool set = Native.SetProcessAffinityMask(h, (UIntPtr)mask);
                bool got2 = Native.GetProcessAffinityMask(h, out back, out sys2);
                bool restored = got && Native.SetProcessAffinityMask(h, orig);
                r = string.Format("orig=0x{0:X} set={1} back=0x{2:X} restored={3}",
                    got ? orig.ToUInt64() : 0, set, got2 ? back.ToUInt64() : 0, restored);
                Native.CloseHandle(h);
            }
        }
        try { File.WriteAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_isotest.txt"), r); } catch { }
        return 0;
    }

    static int IsoEngageCli(string name)
    {
        string r = Iso.TestEngage(name);
        try { File.WriteAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_isoengage.txt"), r); } catch { }
        return 0;
    }

    // 诊断 -isowatch：直接起 ETW 监听→拉一个短进程→报告事件计数（混淆排障用）
    static int IsoWatchCli()
    {
        int starts = 0, stops = 0;
        EtwProc.Started += (pid, name) => starts++;
        EtwProc.Stopped += pid => stops++;
        bool ok = EtwProc.Start();
        string r = "etwStart=" + ok + " err=[" + EtwProc.Error + "]";
        if (ok)
        {
            try
            {
                var p = Process.Start(new ProcessStartInfo { FileName = "cmd.exe", Arguments = "/c ver", CreateNoWindow = true, UseShellExecute = false, WindowStyle = ProcessWindowStyle.Hidden });
                if (p != null) p.Dispose();
            }
            catch { }
            Thread.Sleep(4000);
            EtwProc.Stop();
            r += " starts=" + starts + " stops=" + stops;
        }
        try { File.WriteAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_isowatch.txt"), r); } catch { }
        return 0;
    }

    // 诊断 -irqenum：枚举中断隔离设备及当前亲和状态
    static int IrqEnumCli()
    {
        Cfg.Load();
        Topo.Detect();
        var sb = new System.Text.StringBuilder();
        ulong isoZ, gameZ;
        Iso.Zones(out isoZ, out gameZ);
        sb.AppendLine("isoMode=" + (Cfg.IsoSoft == 1 ? "soft" : "hard") + " irqMode=" + (Cfg.IrqMode ?? "(follow)")
            + " isoZone=0x" + isoZ.ToString("X") + " irqMask=0x" + Cfg.IrqMask.ToString("X")
            + " effective=0x" + IrqIso.EffectiveMask().ToString("X"));
        foreach (var d in IrqIso.EnumDevices(IrqIso.EffectiveMask()))
            sb.AppendLine(d.Label + " | isolated=" + d.Isolated + " custom=" + d.Custom + " msi=" + d.Msi + " | " + d.FullName + " | " + d.Path);
        try { File.WriteAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_irq.txt"), sb.ToString()); } catch { }
        return 0;
    }

    // 诊断 -irqset <index> <0|1>：按 -irqenum 的索引切换设备中断隔离（无界面测试通道）
    static int IrqSetCli(string sIdx, string sOn)
    {
        int idx;
        string r;
        if (!int.TryParse(sIdx, out idx) || (sOn != "0" && sOn != "1")) r = "usage: -irqset <index> <0|1>";
        else
        {
            Cfg.Load();
            Topo.Detect();
            ulong irq = IrqIso.EffectiveMask();
            var devs = IrqIso.EnumDevices(irq);
            if (idx < 0 || idx >= devs.Count) r = "index out of range (count=" + devs.Count + ")";
            else
            {
                var d = devs[idx];
                r = IrqIso.SetIsolated(d, sOn == "1", irq);
                IrqIso.Refresh(d, irq);
                r += " | now isolated=" + d.Isolated + " custom=" + d.Custom;
            }
        }
        try { File.WriteAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_irqset.txt"), r); } catch { }
        return 0;
    }

    void MessageLoop()
    {
        MSG m;
        while (GetMessageW(out m, IntPtr.Zero, 0, 0))
        {
            TranslateMessage(ref m);
            DispatchMessageW(ref m);
        }
    }

    // 显示/电源类广播：滤镜兜底重铺（后台线程，别占消息循环）


    IntPtr RawWndProc(IntPtr h, uint msg, IntPtr w, IntPtr l)
    {
        if (msg == WM_HOTKEY && w.ToInt32() == HOTKEY_ID)
        {
            new Thread(() => DoPurge("热键", false)) { IsBackground = true }.Start();
            return IntPtr.Zero;
        }
        if (msg == WM_TRAY)
        {
            int m = l.ToInt32();
            if (m == WM_LBUTTONDBLCLK) ShowMain();
            else if (m == WM_RBUTTONUP) ShowTrayMenu();
            return IntPtr.Zero;
        }
        if (msg == WM_COMMAND)
        {
            int id = w.ToInt32() & 0xFFFF;
            if (id == MI_OPEN) { ShowMain(); EnsureTrayAlive(); }
            else if (id == MI_PURGE) new Thread(() => DoPurge("手动", false)) { IsBackground = true }.Start();
            else if (id == MI_EXIT) ExitApp();
            return IntPtr.Zero;
        }
        if (msg == shellHookMsg)
        {
            int sc = w.ToInt32();
            if (sc == 1) OnShellWindowCreated(l);
            else if (sc == 4 || sc == 0x8004) { NoteForegroundActive(l); CheckStandbyThreshold(); Iso.OnWindowActive(); FirstCore.OnWindowActive(); }
            return IntPtr.Zero;
        }
        if (msg == taskbarCreatedMsg)
        {
            try { var tnid = BuildTrayNid(); Shell_NotifyIconW(NIM_ADD, ref tnid); } catch { }
            return IntPtr.Zero;
        }
        return DefWindowProcW(h, msg, w, l);
    }

    void ExitApp()
    {
        CloseTrayMenu();
        running = false;
        _monRun = false;
        try { _tuner.Stop(); } catch { }
        _gameLoad.Stop();
        _dpc.Stop();
        _engine.Release();
        Iso.Shutdown();
        FirstCore.Shutdown();
        Slice.CloseAll();
        Native.DeregisterShellHookWindow(msgHwnd);
        var nid = new NID { cbSize = Marshal.SizeOf(typeof(NID)), hWnd = msgHwnd, uID = 1 };
        Shell_NotifyIconW(NIM_DELETE, ref nid);
        if (trayIcon != IntPtr.Zero) DestroyIcon(trayIcon);
        PostQuitMessage(0);
    }

    /* ---------------- 主界面（现建现毁） ---------------- */
    Border[] tabBtns; TextBlock[] tabTexts; Grid[] pages;
    Border tabInd; Grid tabStrip;   // Tab 滑动指示条（单条）与其容器
    bool _indPlaced;                // 指示条是否已测量放置过
    int curTab = -1;
    Button btnPreset; Border presetMenu, presetToast; TextBlock presetToastText;
    bool _presetOpen;
    System.Windows.Threading.DispatcherTimer _toastHold;

    void ShowMain()
    {
        if (win != null) { win.Activate(); return; }
        BuildWindow();
        win.Show();
        if (!_dpc.Ok) StartDpc(true);   // 开窗=观测档重拉（启动失败/重连失败后再开窗时）
    }

    void BuildWindow()
    {
        win = (Window)XamlReader.Parse(XAML);
        uiDisp = win.Dispatcher;
        tabBtns = new[] { (Border)win.FindName("tabTimer"), (Border)win.FindName("tabMem"), (Border)win.FindName("tabSlice") };
        tabTexts = new[] { (TextBlock)win.FindName("tabTimerText"), (TextBlock)win.FindName("tabMemText"), (TextBlock)win.FindName("tabSliceText") };
        tabStrip = (Grid)win.FindName("tabStrip");
        tabInd = (Border)win.FindName("tabInd");
        pages = new[] { (Grid)win.FindName("pageTimer"), (Grid)win.FindName("pageMem"), (Grid)win.FindName("pageSlice") };
        for (int i = 0; i < 3; i++)
        {
            int idx = i;
            tabBtns[i].MouseLeftButtonUp += (s, e) => SelectTab(idx);
            tabBtns[i].MouseEnter += (s, e) => { if (curTab != idx) tabTexts[idx].Foreground = Brush("#666666"); };
            tabBtns[i].MouseLeave += (s, e) => { if (curTab != idx) tabTexts[idx].Foreground = Brush("#888888"); };
        }

        var titleBar = (Border)win.FindName("titleBar");
        titleBar.MouseLeftButtonDown += (s, e) =>
        {
            var src = e.OriginalSource as DependencyObject;
            while (src != null) { if (src is Button) return; src = VisualTreeHelper.GetParent(src); }
            try { win.DragMove(); } catch { }
        };
        ((Button)win.FindName("btnMin")).Click += (s, e) => win.Close();
        ((Button)win.FindName("btnClose")).Click += (s, e) => win.Close();

        btnPreset = (Button)win.FindName("btnPreset");
        presetMenu = (Border)win.FindName("presetMenu");
        presetToast = (Border)win.FindName("presetToast");
        presetToastText = (TextBlock)win.FindName("presetToastText");
        var pmLoad = (Button)win.FindName("pmLoad");
        var pmSave = (Button)win.FindName("pmSave");
        var pmAuto = (Button)win.FindName("pmAuto");
        btnPreset.Click += (s, e) => TogglePresetMenu();
        pmLoad.Click += (s, e) => { HidePresetMenu(); PresetLoad(); };
        pmSave.Click += (s, e) => { HidePresetMenu(); PresetSave(); };
        pmAuto.Click += (s, e) => SetAutostart(!IsAutostart());
        win.PreviewMouseDown += (s, e) =>
        {
            if (!_presetOpen) return;
            var src = e.OriginalSource as DependencyObject;
            if (InTree(src, presetMenu) || InTree(src, btnPreset)) return;
            HidePresetMenu();
        };

        lblVal = (TextBlock)win.FindName("lblVal");
        lblRes = (TextBlock)win.FindName("lblRes");
        lblSlept = (TextBlock)win.FindName("lblSlept");
        lblStatus = (TextBlock)win.FindName("lblStatus");
        pb = (ProgressBar)win.FindName("pb");
        banner = (Border)win.FindName("banner");
        bannerText = (TextBlock)win.FindName("bannerText");
        btnStart = (Button)win.FindName("btnStart");
        btnStop = (Button)win.FindName("btnStop");
        btnTimerMode = (Button)win.FindName("btnTimerMode");
        timerAutoPanel = (StackPanel)win.FindName("timerAutoPanel");
        timerManualPanel = (StackPanel)win.FindName("timerManualPanel");
        tbTimerManual = (TextBox)win.FindName("tbTimerManual");
        autoCheck = (System.Windows.Shapes.Path)win.FindName("pmAutoCheck");
        dpcGraphHost = (Grid)win.FindName("dpcGraphHost");
        lblDpcAvg = (TextBlock)win.FindName("lblDpcAvg");
        lblDpcMax = (TextBlock)win.FindName("lblDpcMax");
        lblDpcMin = (TextBlock)win.FindName("lblDpcMin");
        lblDpcState = (TextBlock)win.FindName("lblDpcState");
        if (_graph == null) _graph = new DpcGraph();
        dpcGraphHost.Children.Add(_graph);
        btnStart.Click += (s, e) => StartTest();
        btnStop.Click += (s, e) => { _tuner.Stop(); _gameLoad.Stop(); FlushDebugLog(); SetRunningUI(false); ResumeIdleLoops(); };
        btnTimerMode.Click += (s, e) => SetTimerMode(!timerManualMode);
        ((Button)win.FindName("btnManualApply")).Click += (s, e) => ApplyManualTimer();
        tbTimerManual.KeyDown += (s, e) => { if (e.Key == Key.Enter) { ApplyManualTimer(); e.Handled = true; } };
        SetTimerMode(false);
        lblVal.Text = _engine.Holding ? _engine.AppliedValue.ToString() : "—";
        lblRes.Text = string.Format("{0:F4}ms", _engine.CurrentResolution() / 10000.0);
        lblStatus.Text = _tuner.Running ? "测试运行中…" : (_engine.Holding ? "已应用预设" : "就绪");
        lblDpcState.Text = DpcStateText();
        SetRunningUI(_tuner.Running);
        if (_dpc.Ok) StartDpcTimer();
        if (_presetBannerPending)
        {
            _presetBannerPending = false;
            banner.Visibility = Visibility.Visible;
            bannerText.Text = string.Format("已应用预设：设定值 {0}（Resolution {1:F4}ms）。点击「开始自动测试」可重新测定。",
                _engine.AppliedValue, _engine.CurrentResolution() / 10000.0);
        }
        RefreshAutoVisual();
        if (_tuner.Running) MonPause(); else MonResume();

        standbyNum = (TextBlock)win.FindName("standbyNum");
        memInfo = (TextBlock)win.FindName("memInfo");
        memRatioText = (TextBlock)win.FindName("memRatioText");
        memRatioBar = (Border)win.FindName("memRatioBar");
        lblLastPurge = (TextBlock)win.FindName("lblLastPurge");
        tbThreshold = (TextBox)win.FindName("tbThreshold");
        tbInterval = (TextBox)win.FindName("tbInterval");
        pillOff = (Border)win.FindName("pillOff"); pillSmart = (Border)win.FindName("pillSmart");
        pillTimer = (Border)win.FindName("pillTimer");
        tglHotkey = (Border)win.FindName("tglHotkey");
        knobHotkey = (System.Windows.Shapes.Ellipse)win.FindName("knobHotkey");
        ((Button)win.FindName("btnPurge")).Click += (s, e) =>
        {
            lblLastPurge.Text = "清理中…";
            new Thread(() => DoPurge("手动", false)) { IsBackground = true }.Start();
        };
        ((Button)win.FindName("btnRefresh")).Click += (s, e) => RefreshMemStats();
        pillOff.MouseLeftButtonUp += (s, e) => SetMemMode("off");
        pillSmart.MouseLeftButtonUp += (s, e) => SetMemMode("smart");
        pillTimer.MouseLeftButtonUp += (s, e) => SetMemMode("timer");
        HookPillHover(pillOff, "off"); HookPillHover(pillSmart, "smart"); HookPillHover(pillTimer, "timer");
        RefreshPills();
        tbThreshold.Text = thresholdMB.ToString();
        tbInterval.Text = intervalMin.ToString();
        tbThreshold.LostFocus += (s, e) =>
        {
            int v; if (int.TryParse(tbThreshold.Text, out v)) thresholdMB = Math.Max(128, Math.Min(65536, v));
            tbThreshold.Text = thresholdMB.ToString(); Cfg.SaveKey("Threshold", thresholdMB.ToString());
        };
        tbInterval.LostFocus += (s, e) =>
        {
            int v; if (int.TryParse(tbInterval.Text, out v)) intervalMin = Math.Max(1, Math.Min(1440, v));
            tbInterval.Text = intervalMin.ToString(); Cfg.SaveKey("Interval", intervalMin.ToString()); ApplyMemMode();
        };
        SetToggle(tglHotkey, knobHotkey, hotkeyEnabled);
        tglHotkey.MouseLeftButtonUp += (s, e) =>
        {
            hotkeyEnabled = !hotkeyEnabled;
            SetToggle(tglHotkey, knobHotkey, hotkeyEnabled);
            ApplyHotkey();
            Cfg.SaveKey("Hotkey", hotkeyEnabled ? "1" : "0");
        };
        lblLastPurge.Text = lastPurgeMsg.Length > 0 ? lastPurgeMsg : "最近清理：—";
        RefreshMemStats();
        memLiveTimer = new System.Windows.Threading.DispatcherTimer { Interval = TimeSpan.FromSeconds(2) };
        memLiveTimer.Tick += (s, e) => RefreshMemStats();
        memLiveTimer.Start();

        procList = (ListBox)win.FindName("procList");
        tbSearch = (TextBox)win.FindName("tbSearch");
        cbFilter = (ComboBox)win.FindName("cbFilter");
        lblSliceMsg = (TextBlock)win.FindName("lblSliceMsg");
        if (lastSliceMsg.Length > 0) lblSliceMsg.Text = lastSliceMsg;
        cbFilter.ItemsSource = new[] { "全部进程", "仅有窗口", "仅规则" };
        cbFilter.SelectionChanged += (s, e) => { if (!_populating) RefillProcs(); };
        cbFilter.SelectedIndex = 0;
        searchDebounce = new System.Windows.Threading.DispatcherTimer { Interval = TimeSpan.FromMilliseconds(300) };
        searchDebounce.Tick += (s, e) => { searchDebounce.Stop(); RefillProcs(); };
        tbSearch.TextChanged += (s, e) => { searchDebounce.Stop(); searchDebounce.Start(); };
        ((Button)win.FindName("btnRefreshProc")).Click += (s, e) => RefillProcs();
        tbW32Sep = (TextBox)win.FindName("tbW32Sep");
        uint? w32cur = W32SepRead();
        if (w32cur.HasValue) tbW32Sep.Text = w32cur.Value.ToString();
        tbW32Sep.KeyDown += (s, e) => { if (e.Key == Key.Enter) W32SepApply(); };
        ((Button)win.FindName("btnW32Sep")).Click += (s, e) => W32SepApply();
        lblIsoState = (TextBlock)win.FindName("lblIsoState");
        isoCcdHost = (StackPanel)win.FindName("isoCcdHost");
        isoCoreHost = (StackPanel)win.FindName("isoCoreHost");
        isoModeHost = (StackPanel)win.FindName("isoModeHost");
        BuildIsoPanel();

        win.Closed += (s, e) =>
        {
            if (_dpcTimer != null) { _dpcTimer.Stop(); _dpcTimer = null; }
            if (_dpcKeepAlive || _autoDriver)
            {
                bool needStreamOff = Cfg.DpcStreamOff == 1;
                bool wrong = !_dpc.Ok || _dpc.ActiveIntervalUs != Cfg.DpcInterval || (needStreamOff && !_dpc.StreamOffActive) || (!needStreamOff && _dpc.StreamOffActive);
                if (wrong && !_dpcStarting) Task.Run(() => _dpc.Start(Cfg.DpcInterval, needStreamOff));
            }
            else if (_dpc.Ok) _dpc.Stop();
            if (memLiveTimer != null) { memLiveTimer.Stop(); memLiveTimer = null; }
            if (_graph != null && dpcGraphHost != null) dpcGraphHost.Children.Remove(_graph);
            MonPause();
            win = null;
            tabBtns = null; tabTexts = null; tabInd = null; tabStrip = null; pages = null;
            _indPlaced = false;
            lblVal = lblRes = lblSlept = lblStatus = bannerText = null;
            lblDpcAvg = lblDpcMax = lblDpcMin = lblDpcState = null;
            btnStart = btnStop = btnTimerMode = null;
            timerAutoPanel = timerManualPanel = null; tbTimerManual = null; timerManualMode = false;
            pb = null; banner = null; autoCheck = null; dpcGraphHost = null;
            standbyNum = memInfo = memRatioText = lblLastPurge = null;
            memRatioBar = pillOff = pillSmart = pillTimer = tglHotkey = null;
            knobHotkey = null; tbThreshold = tbInterval = null;
            if (searchDebounce != null) { searchDebounce.Stop(); searchDebounce = null; }
            _presetOpen = false;
            btnPreset = null; presetMenu = null; presetToast = null; presetToastText = null;
            if (_toastHold != null) { _toastHold.Stop(); _toastHold = null; }
            procList = null; tbSearch = null; cbFilter = null; lblSliceMsg = null; tbW32Sep = null;
            if (_isoStatusHandler != null) { Iso.StatusChanged -= _isoStatusHandler; _isoStatusHandler = null; }
            lblIsoState = null; isoCcdHost = null;
            isoCoreHost = null; isoModeHost = null;
            _isoModeCombo = null; _softZoneTabGame = _softZoneTabIso = null;
            _isoBoxes.Clear(); _softBoxes.Clear();
            _irqChips.Clear();
            _sliceFilled = false;
            curTab = -1;
            GC.Collect();
            GC.WaitForPendingFinalizers();
            EmptyWorkingSet(GetCurrentProcess());
        };
        SelectTab(startTab >= 1 && startTab <= 3 ? startTab - 1 : 0);
        win.Loaded += (s, e) => { _indPlaced = false; PlaceInd(curTab, false); };
    }

    /* ---------------- 预设档案（载入 / 导出，右上角 ⇅ 菜单） ---------------- */
    // 预设有意只带"用户规则"，不含 value/resolution（本机测定的计时器值，跨机无意义）与 Dpc* 实验档
    void TogglePresetMenu() { if (_presetOpen) HidePresetMenu(); else ShowPresetMenu(); }

    void ShowPresetMenu()
    {
        if (presetMenu == null) return;
        _presetOpen = true;
        RefreshAutoVisual();                // 每次展开都按注册表实况刷新勾选
        // 瞬开：入场位移手动帧动画已砍（10-19 用户反馈卡顿）；也避免动画时钟请求 1ms 分辨率
        presetMenu.Opacity = 1;
        presetMenu.RenderTransform = null;
        presetMenu.Visibility = Visibility.Visible;
    }

    void HidePresetMenu()
    {
        _presetOpen = false;
        if (presetMenu == null) return;
        presetMenu.Visibility = Visibility.Collapsed;
    }

    static bool InTree(DependencyObject node, DependencyObject root)
    {
        if (root == null) return false;
        try   // OriginalSource 可能是非 Visual（Run 等），VisualTreeHelper.GetParent 会抛——不能让它崩在点击处理器里
        {
            while (node != null) { if (node == root) return true; node = VisualTreeHelper.GetParent(node); }
        }
        catch { }
        return false;
    }

    // 结果轻提示（浅底深字，3 秒自动收起；连发时重置计时）
    void ShowToast(string msg)
    {
        if (presetToast == null) return;
        presetToastText.Text = msg;
        var m = presetToast;
        m.Opacity = 1;
        m.Visibility = Visibility.Visible;
        var tt = new TranslateTransform(0, -6);
        m.RenderTransform = tt;
        int frame = 0;
        var anim = new System.Windows.Threading.DispatcherTimer { Interval = TimeSpan.FromMilliseconds(15) };
        anim.Tick += (s, e) =>
        {
            frame++;
            double t = frame / 6.0;
            if (t >= 1) { t = 1; anim.Stop(); }
            double ease = 1 - (1 - t) * (1 - t);
            tt.Y = -6 * (1 - ease);
        };
        anim.Start();
        if (_toastHold != null) { _toastHold.Stop(); _toastHold = null; }
        _toastHold = new System.Windows.Threading.DispatcherTimer { Interval = TimeSpan.FromSeconds(3.2) };
        _toastHold.Tick += (s, e) =>
        {
            _toastHold.Stop(); _toastHold = null;
            if (presetToast != null) presetToast.Visibility = Visibility.Collapsed;
        };
        _toastHold.Start();
    }

    static string PresetDir() { return Path.Combine(Cfg.Dir, "presets"); }

    void PresetSave()
    {
        try
        {
            Directory.CreateDirectory(PresetDir());
            var dlg = new Microsoft.Win32.SaveFileDialog
            {
                Title = "导出预设",
                Filter = "DunSuite Lite 预设 (*.dunpreset)|*.dunpreset|文本文件 (*.txt)|*.txt",
                DefaultExt = ".dunpreset",
                AddExtension = true,
                FileName = "DunSuiteLite调度_" + DateTime.Now.ToString("MMdd_HHmm"),
                InitialDirectory = PresetDir()
            };
            if (dlg.ShowDialog(win) != true) return;
            var lines = Cfg.ExportPresetLines(PresetScope.Schedule);
            var all = new List<string>
            {
                "#DUNSUITELITE-PRESET 1",
                "#SCOPE=SCHEDULE",
                "#CPU=" + Topo.LogicalCount,
                "#DATE=" + DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss")
            };
            all.AddRange(lines);
            File.WriteAllLines(dlg.FileName, all.ToArray());
            ShowToast("已导出 " + lines.Count + " 项规则");
            SliceMsg("预设已导出：" + Path.GetFileName(dlg.FileName) + "（" + lines.Count + " 项）");
        }
        catch (Exception ex) { ShowToast("导出失败：" + ex.Message); }
    }

    static List<string> PresetParseLines(string[] raw, out int cpu, out int clipped, out int skipped)
    {
        cpu = 0; clipped = 0; skipped = 0;
        var kv = new List<string>();
        foreach (var line in raw)
        {
            var t = line.Trim();
            if (t.Length == 0) continue;
            if (t[0] == '#')
            {
                int n;
                if (t.StartsWith("#CPU=", StringComparison.OrdinalIgnoreCase) && int.TryParse(t.Substring(5).Trim(), out n)) cpu = n;
                continue;
            }
            int eq = t.IndexOf('=');
            if (eq <= 0) continue;
            string k = t.Substring(0, eq).Trim();
            if (!Cfg.IsPresetKey(k)) continue;
            string v = t.Substring(eq + 1).Trim();
            if (cpu > 0 && cpu != Topo.LogicalCount && Cfg.IsMaskKey(k))
            {
                ulong m;
                if (ulong.TryParse(v, System.Globalization.NumberStyles.HexNumber, null, out m))
                {
                    ulong cl = m & Topo.AllMask;
                    bool collapsed = cl == Topo.AllMask && !k.StartsWith("IRQ", StringComparison.OrdinalIgnoreCase);
                    if (cl == 0 || collapsed)
                    {
                        ulong cur = Cfg.MaskValue(k) & Topo.AllMask;
                        if (collapsed) skipped++; else clipped++;
                        if (cur == 0) continue;
                        t = k + "=" + cur.ToString("X");
                    }
                    else
                    {
                        if (cl != m) clipped++;
                        t = k + "=" + cl.ToString("X");
                    }
                }
                kv.Add(t);
                continue;
            }
            if (k.StartsWith("FC_", StringComparison.OrdinalIgnoreCase))
            {
                int cn;
                if (!int.TryParse(v, out cn) || cn < 0 || cn >= Topo.LogicalCount) { skipped++; continue; }
            }
            kv.Add(t);
        }
        return kv;
    }

    void PresetLoad()
    {
        try
        {
            Directory.CreateDirectory(PresetDir());
            var dlg = new Microsoft.Win32.OpenFileDialog
            {
                Title = "载入预设",
                Filter = "DunSuite Lite 预设 (*.dunpreset)|*.dunpreset|所有文件 (*.*)|*.*",
                CheckFileExists = true,
                InitialDirectory = PresetDir()
            };
            if (dlg.ShowDialog(win) != true) return;
            var raw = File.ReadAllLines(dlg.FileName);
            int cpu, clipped, skipped;
            var kv = PresetParseLines(raw, out cpu, out clipped, out skipped);
            if (kv.Count == 0) { ShowToast("文件里没有简化版可用规则"); return; }
            int n2 = Cfg.ImportPresetLines(kv, PresetScope.Schedule);
            if (n2 == 0) { ShowToast("载入失败：配置写入异常"); return; }
            PresetAfterImport();
            string tip = "已载入 " + n2 + " 项调度规则";
            if (clipped > 0 || skipped > 0) tip += "（调整 " + clipped + " 项，跳过 " + skipped + " 项）";
            ShowToast(tip);
            SliceMsg("预设已载入：" + Path.GetFileName(dlg.FileName) + "（" + n2 + " 项）· 重启 DunSuite Lite 可全量补套");
        }
        catch (Exception ex) { ShowToast("载入失败：" + ex.Message); }
    }

    void PresetAfterImport()
    {
        try { Iso.MaskChanged(); FollowIsoSelf(); } catch { }
        ApplySliceRulesToRunning();
        if (win == null) return;
        memMode = Cfg.MemMode; thresholdMB = Cfg.MemThreshold;
        intervalMin = Cfg.MemInterval; hotkeyEnabled = Cfg.MemHotkey;
        if (tbThreshold != null) tbThreshold.Text = thresholdMB.ToString();
        if (tbInterval != null) tbInterval.Text = intervalMin.ToString();
        RefreshPills();
        if (tglHotkey != null) SetToggle(tglHotkey, knobHotkey, hotkeyEnabled);
        ApplyMemMode(); ApplyHotkey();
        BuildIsoModeCombo();
        RebuildIsoCoreRows();
        ulong irqNow = IrqIso.EffectiveMask();
        foreach (var chip in _irqChips) { var d = (IrqIso.Dev)chip.Tag; IrqIso.Refresh(d, irqNow); StyleIrqChip(chip, d); }
        UpdateIrqMaskBtn();
        if (_sliceFilled && procList != null) RefillProcs();
    }

    bool _sliceFilled;   // 每个窗口会话只懒填一次

    void SelectTab(int i)
    {
        if (curTab == i) return;
        curTab = i;
        if (i == 2 && !_sliceFilled) { _sliceFilled = true; RefillProcs(); }
        for (int k = 0; k < 3; k++)
        {
            bool on = k == i;
            tabTexts[k].Foreground = Brush(on ? "#111111" : "#888888");
            pages[k].Visibility = on ? Visibility.Visible : Visibility.Collapsed;
        }
        PlaceInd(i, false);   // 指示条瞬移（切页动画已砍：10-13 用户拍板，VM 复现不了的动画卡顿不再追，瞬时切换一了百了）
        // 页面瞬切：Visibility 已由上方循环切换；历史动画（Opacity/位移手动帧）已全部停用
        var p = pages[i];
        p.Opacity = 1;
        p.RenderTransform = null;
    }

    // Tab 指示条定位：TranslatePoint 量目标中心 → 直接瞬移（滑动画已砍，10-13 用户拍板瞬时切换）
    void PlaceInd(int i, bool animate)
    {
        if (tabInd == null || tabStrip == null || tabBtns == null) return;
        if (tabStrip.ActualWidth <= 0) return;   // 未排版：等 Loaded 瞬移
        double target;
        try
        {
            var pt = tabBtns[i].TranslatePoint(new Point(0, 0), tabStrip);
            target = pt.X + (tabBtns[i].ActualWidth - tabInd.Width) / 2;
        }
        catch { return; }
        tabInd.Margin = new Thickness(target, 0, 0, 0);
        _indPlaced = true;
    }

    /* ---------------- 时间片模块（页3 + WMI 监听） ---------------- */
    // 系统关键进程与 Lite 自身不进入进程调优列表。
    static readonly HashSet<string> _sliceNoTouch = new HashSet<string>(StringComparer.OrdinalIgnoreCase)
    {
        "system", "smss", "csrss", "wininit", "winlogon", "services", "lsass", "lsaiso",
        "svchost", "dwm", "dunsuitelite", "memory compression", "registry", "secure system", "idle"
    };

    // 时间片规则通道：Shell Hook 窗口创建推送（OnShellWindowCreated）+ 启动时存量补套 + 加规则即时补套
    // ——无轮询无线程（2026-08-16 删 SliceWatchLoop；盲区=后启动的无窗口规则进程，游戏场景碰不到）
    readonly Dictionary<int, DateTime> _sliceApplied = new Dictionary<int, DateTime>();   // PID+StartTime 去重

    void ApplyRuleToProc(Process p, int idx, string key, bool quiet)
    {
        try
        {
            lock (_sliceApplied)
            {
                DateTime st;
                if (_sliceApplied.TryGetValue(p.Id, out st) && st == p.StartTime) return;
                _sliceApplied[p.Id] = p.StartTime;
            }
            string r = Slice.Apply(p.Id, idx);
            if (!quiet) SliceMsg(key + ".exe 启动 → 自动套用「" + Slice.LevelNames[idx] + "」" + (r == "OK" ? " ✓" : " ✗ " + r));
        }
        catch { }
    }

    // 启动时对已在跑的规则进程补套档位
    void ApplySliceRulesToRunning()
    {
        foreach (var kv in SnapshotSliceRules())
        {
            if (kv.Value <= 0) continue;
            Process[] procs;
            try { procs = Process.GetProcessesByName(kv.Key); } catch { continue; }
            foreach (var p in procs)
            {
                ApplyRuleToProc(p, kv.Value, kv.Key, true);
                p.Dispose();
            }
        }
    }

    // Shell Hook 主通道：任何进程创建顶级窗口时系统主动推送（零轮询、秒级生效）。
    // 盲区：控制台/服务进程的窗口归 conhost 等宿主，抓不到——由 60s 兜底轮询覆盖。
    void OnShellWindowCreated(IntPtr hwnd)
    {
        try
        {
            CheckStandbyThreshold();   // 待机阈值顺带查（必须早于规则秒退，否则无规则时永不检查）
            var rules = SnapshotSliceRules();
            if (rules.Count == 0) return;   // 无规则秒退，每个窗口创建事件的平均开销≈零
            uint pid;
            Native.GetWindowThreadProcessId(hwnd, out pid);
            if (pid == 0 || (int)pid == _selfPid) return;
            Process p;
            try { p = Process.GetProcessById((int)pid); } catch { return; }   // 窗口宿主已退出
            try
            {
                string n = p.ProcessName;
                foreach (var kv in rules)
                {
                    if (kv.Value > 0 && string.Equals(n, kv.Key, StringComparison.OrdinalIgnoreCase))
                    {
                        ApplyRuleToProc(p, kv.Value, kv.Key, false);
                        break;
                    }
                }
            }
            finally { p.Dispose(); }
        }
        catch { }
    }

    // 改规则时即时补套已在跑的同名进程（替代轮询的延迟补套；规则名字级，展开行单独改档时靠它同步其余实例）
    void ApplyRuleByName(string name, int lv)
    {
        try
        {
            foreach (var p in Process.GetProcessesByName(name))
            {
                ApplyRuleToProc(p, lv, name, false);
                p.Dispose();
            }
        }
        catch { }
    }

    static List<KeyValuePair<string, int>> SnapshotSliceRules()
    {
        lock (Cfg.SliceRules) return new List<KeyValuePair<string, int>>(Cfg.SliceRules);
    }

    string lastSliceMsg = "";

    void SliceMsg(string m)
    {
        lastSliceMsg = m;   // 托盘期窗口不在也留痕，下次开窗补显示
        Ui(() => { if (lblSliceMsg != null) lblSliceMsg.Text = m; });
    }

    /* ---------------- Win32PrioritySeparation（原 Win32 设置工具并入页3） ---------------- */
    static uint? W32SepRead()
    {
        try
        {
            using (var k = Microsoft.Win32.Registry.LocalMachine.OpenSubKey(@"SYSTEM\CurrentControlSet\Control\PriorityControl"))
            {
                if (k == null) return null;
                object v = k.GetValue("Win32PrioritySeparation");
                return v == null ? (uint?)null : Convert.ToUInt32(v);
            }
        }
        catch { return null; }
    }

    static bool W32SepTryParse(string s, out uint v)   // 十进制或 0x 前缀十六进制
    {
        v = 0;
        if (string.IsNullOrWhiteSpace(s)) return false;
        s = s.Trim();
        if (s.StartsWith("0x", StringComparison.OrdinalIgnoreCase))
            return uint.TryParse(s.Substring(2), System.Globalization.NumberStyles.HexNumber,
                System.Globalization.CultureInfo.InvariantCulture, out v);
        return uint.TryParse(s, out v);
    }

    void W32SepApply()
    {
        if (tbW32Sep == null) return;
        uint v;
        if (!W32SepTryParse(tbW32Sep.Text, out v)) { SliceMsg("Win32 分离值：输入无效（十进制或 0x 十六进制）"); return; }
        try
        {
            using (var k = Microsoft.Win32.Registry.LocalMachine.CreateSubKey(
                @"SYSTEM\CurrentControlSet\Control\PriorityControl", true))
                k.SetValue("Win32PrioritySeparation", v, Microsoft.Win32.RegistryValueKind.DWord);
            tbW32Sep.Text = v.ToString();
            SliceMsg("Win32 分离值已写入 " + v + " (0x" + v.ToString("X8") + ")，重启后生效");
        }
        catch (Exception ex) { SliceMsg("Win32 分离值写入失败：" + ex.Message); }
    }

    static int ClassToLevel(int sc) { return 10 - sc; }   // LevelClass={-1,9,8,...,0}：level=10-sc

    void RefillProcs()
    {
        if (procList == null) return;
        _populating = true;
        try
        {
            procList.Items.Clear();
            string search = tbSearch.Text.Trim();
            int filter = cbFilter.SelectedIndex;
            var procs = new List<Process>();
            foreach (var p in Process.GetProcesses())
            {
                try
                {
                    string n = p.ProcessName;
                    if (_sliceNoTouch.Contains(n)) { p.Dispose(); continue; }
                    if (search.Length > 0 && n.IndexOf(search, StringComparison.OrdinalIgnoreCase) < 0) { p.Dispose(); continue; }
                    if (filter == 1 && p.MainWindowHandle == IntPtr.Zero) { p.Dispose(); continue; }
                    if (filter == 2 && !Cfg.SliceRules.ContainsKey(n) && Cfg.IsoRuleMode(n) == 0 && !Cfg.FcRules.ContainsKey(n)) { p.Dispose(); continue; }
                    procs.Add(p);
                }
                catch { p.Dispose(); }
            }
            var comboStyle = (Style)win.FindResource("SliceCombo");
            var seen = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
            var byName = new Dictionary<string, List<Process>>(StringComparer.OrdinalIgnoreCase);
            foreach (var p in procs)
            {
                seen.Add(p.ProcessName);
                List<Process> lst;
                if (!byName.TryGetValue(p.ProcessName, out lst)) { lst = new List<Process>(); byName[p.ProcessName] = lst; }
                lst.Add(p);
            }
            var groupNames = new List<string>(byName.Keys);
            groupNames.Sort(StringComparer.OrdinalIgnoreCase);
            foreach (var n in groupNames)
            {
                var lst = byName[n];
                if (lst.Count == 1) AddProcRow(lst[0], comboStyle);
                else
                {
                    AddProcRow(null, comboStyle, null, lst);
                    if (_expanded.Contains(n))
                        foreach (var p in lst) AddProcRow(p, comboStyle, null, null, true);
                }
                foreach (var p in lst) p.Dispose();
            }
            if (filter == 2)
            {
                var ghosts = new SortedSet<string>(StringComparer.OrdinalIgnoreCase);
                lock (Cfg.SliceRules) foreach (var n in Cfg.SliceRules.Keys) ghosts.Add(n);
                lock (Cfg.IsoGames) foreach (var n in Cfg.IsoGames) ghosts.Add(n);
                lock (Cfg.IsoBackgrounds) foreach (var n in Cfg.IsoBackgrounds) ghosts.Add(n);
                lock (Cfg.FcRules) foreach (var n in Cfg.FcRules.Keys) ghosts.Add(n);
                foreach (var n in ghosts)
                {
                    if (seen.Contains(n) || _sliceNoTouch.Contains(n)) continue;
                    if (search.Length > 0 && n.IndexOf(search, StringComparison.OrdinalIgnoreCase) < 0) continue;
                    AddProcRow(null, comboStyle, n);
                }
            }
        }
        finally { _populating = false; }
    }

    void AddProcRow(Process p, Style comboStyle, string ghostName = null, List<Process> group = null, bool indent = false)
    {
        bool running = p != null;
        bool groupMode = group != null;
        string name = groupMode ? group[0].ProcessName : (running ? p.ProcessName : ghostName);
        int pid = running ? p.Id : -1;
        var pids = new List<int>();
        if (groupMode) foreach (var tp in group) pids.Add(tp.Id);
        bool inJob;
        int curClass = running ? Slice.QueryClass(pid, out inJob) : -1;
        bool pinned = Cfg.SliceRules.ContainsKey(name);
        int comboIdx = pinned ? Cfg.SliceRules[name] : (curClass >= 0 ? ClassToLevel(curClass) : 0);

        var row = new Grid { Tag = name };
        row.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(3) });
        row.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
        row.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(76) });
        row.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(82) });
        row.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(62) });

        bool nonDefault = curClass >= 0 && curClass != 5;
        var bar = new Border { CornerRadius = new CornerRadius(1.5), Margin = new Thickness(0, 4, 6, 4) };
        bar.Background = Brush(groupMode ? (pinned ? "#111111" : "#00000000")
            : running ? (nonDefault ? "#111111" : "#00000000")
            : (pinned ? "#D0D0D0" : "#00000000"));
        Grid.SetColumn(bar, 0);
        row.Children.Add(bar);

        var nameStack = new StackPanel { VerticalAlignment = VerticalAlignment.Center };
        var nameText = new TextBlock { Text = name + ".exe", Foreground = Brush(running || groupMode ? "#111111" : "#888888"), FontSize = 12 };
        if (groupMode)
        {
            bool open = _expanded.Contains(name);
            var expBtn = new TextBlock { Text = open ? "-" : "∨", Foreground = Brush("#888888"), FontSize = 9, VerticalAlignment = VerticalAlignment.Center, Margin = new Thickness(6, 0, 0, 0) };
            var nameLine = new StackPanel { Orientation = Orientation.Horizontal, VerticalAlignment = VerticalAlignment.Center, Cursor = Cursors.Hand };
            nameLine.ToolTip = "同名进程组：点击展开/收起实例列表\n规则按软件名生效，组内一起处理";
            nameLine.Children.Add(nameText);
            nameLine.Children.Add(expBtn);
            nameLine.MouseLeftButtonUp += (ss, ee) =>
            {
                if (_expanded.Contains(name)) _expanded.Remove(name); else _expanded.Add(name);
                RefillProcs();
                ee.Handled = true;
            };
            nameStack.Children.Add(nameLine);
        }
        else nameStack.Children.Add(nameText);
        nameStack.Children.Add(new TextBlock { Text = groupMode ? (group.Count + " 个实例") : (running ? "PID " + pid : "未运行"), Foreground = Brush("#888888"), FontSize = 9, Margin = new Thickness(0, 1, 0, 0) });
        if (indent) nameStack.Margin = new Thickness(22, 0, 0, 0);
        Grid.SetColumn(nameStack, 1);
        row.Children.Add(nameStack);

        var combo = new ComboBox
        {
            Style = comboStyle,
            ItemsSource = Slice.LevelNames,
            SelectedIndex = comboIdx,
            VerticalAlignment = VerticalAlignment.Center,
            HorizontalAlignment = HorizontalAlignment.Stretch,
            Margin = new Thickness(0, 0, 8, 0),
            ToolTip = "时间片：改档即记忆，进程启动自动套用\n选「忽略」= 取消记忆并立即还原"
        };
        Grid.SetColumn(combo, 2);
        row.Children.Add(combo);
        NoWheelScroll(combo);

        int isoMode = Cfg.IsoRuleMode(name);
        bool isoGame = isoMode == 1;
        var isoCombo = new ComboBox
        {
            Style = comboStyle,
            VerticalAlignment = VerticalAlignment.Center,
            HorizontalAlignment = HorizontalAlignment.Stretch,
            Margin = new Thickness(0, 0, 8, 0),
            ToolTip = "核心规则：\n前台=进入前台区，并触发其他普通进程收拢进隔离区\n后台=仅该进程进入隔离区，不触发全局收拢\n选 无 = 取消规则并还原"
        };
        isoCombo.Items.Add("无");
        isoCombo.Items.Add("前台");
        isoCombo.Items.Add("后台");
        isoCombo.SelectedIndex = isoMode;
        Grid.SetColumn(isoCombo, 3);
        row.Children.Add(isoCombo);
        NoWheelScroll(isoCombo);

        int fcCore = -1;
        lock (Cfg.FcRules) if (Cfg.FcRules.ContainsKey(name)) fcCore = Cfg.FcRules[name];
        var fcCpus = new List<int>();
        ulong fcPool = Topo.AllMask;
        ulong fcIso, fcGame;
        Iso.Zones(out fcIso, out fcGame);
        if (isoGame) fcPool &= fcGame;
        for (int b = 0; b < Topo.LogicalCount; b++) if ((fcPool & (1UL << b)) != 0) fcCpus.Add(b);
        if (fcCore >= 0 && !fcCpus.Contains(fcCore)) { fcCpus.Add(fcCore); fcCpus.Sort(); }
        var fcCombo = new ComboBox
        {
            Style = comboStyle,
            VerticalAlignment = VerticalAlignment.Center,
            HorizontalAlignment = HorizontalAlignment.Stretch,
            ToolTip = "首核调度：把主线程钉在选的逻辑 CPU 上\n前台规则进程只列前台区；选 无 立即还原"
        };
        fcCombo.Items.Add("关");
        foreach (var c in fcCpus) fcCombo.Items.Add(c.ToString());
        fcCombo.SelectedIndex = fcCore >= 0 ? fcCpus.IndexOf(fcCore) + 1 : 0;
        Grid.SetColumn(fcCombo, 4);
        row.Children.Add(fcCombo);
        NoWheelScroll(fcCombo);
        if (!Topo.Supported || !FirstCore.HardSupported) { fcCombo.IsEnabled = false; fcCombo.ToolTip = "当前系统不支持此功能"; }

        combo.SelectionChanged += (ss, ee) =>
        {
            if (_populating || _syncCb) return;
            int lv = combo.SelectedIndex;
            if (lv < 0) return;
            if (lv == 0)
            {
                lock (Cfg.SliceRules) Cfg.SliceRules.Remove(name);
                Cfg.DeleteKey("TS_" + name);
            }
            else
            {
                lock (Cfg.SliceRules) Cfg.SliceRules[name] = lv;
                Cfg.SaveKey("TS_" + name, lv.ToString());
            }
            if (running || groupMode)
            {
                string r = "OK";
                var targets = groupMode ? pids : new List<int> { pid };
                foreach (var tpid in targets)
                {
                    r = Slice.Apply(tpid, lv);
                    if (r != "OK" && r != "忽略" && r != "已清除") break;
                }
                bool ok = r == "OK" || r == "忽略" || r == "已清除";
                SliceMsg(name + ".exe → 「" + Slice.LevelNames[lv] + "」" + (ok ? " ✓" : " ✗ " + r) + (lv == 0 ? "·已取消记忆" : "·已记忆") + (groupMode ? "（" + group.Count + " 实例）" : ""));
                bool inJ; int cc = groupMode ? -1 : Slice.QueryClass(pid, out inJ);
                bool nd = cc >= 0 && cc != 5;
                bar.Background = Brush(groupMode ? (lv != 0 ? "#111111" : "#00000000") : (nd ? "#111111" : "#00000000"));
                if (!groupMode) ApplyRuleByName(name, lv);
            }
            else if (lv == 0)
            {
                SliceMsg(name + ".exe 未运行——已取消记忆");
                bar.Background = Brush("#00000000");
            }
            else
            {
                SliceMsg(name + ".exe 未运行——规则已记忆「" + Slice.LevelNames[lv] + "」，启动时自动套用");
                bar.Background = Brush("#D0D0D0");
            }
            SyncNameCombo(name, 2, lv);
        };

        isoCombo.SelectionChanged += (ss, ee) =>
        {
            if (_populating || _syncCb) return;
            int sel = isoCombo.SelectedIndex;
            if (sel < 0) return;
            int oldMode = Cfg.IsoRuleMode(name);
            if (oldMode == sel) return;
            lock (Cfg.IsoGames) Cfg.IsoGames.Remove(name);
            lock (Cfg.IsoBackgrounds) Cfg.IsoBackgrounds.Remove(name);
            if (sel == 1)
            {
                lock (Cfg.IsoGames) Cfg.IsoGames.Add(name);
                Cfg.SaveKey("ISO_" + name, "1");
            }
            else if (sel == 2)
            {
                lock (Cfg.IsoBackgrounds) Cfg.IsoBackgrounds.Add(name);
                Cfg.SaveKey("ISO_" + name, "bg");
            }
            else Cfg.DeleteKey("ISO_" + name);
            Iso.RuleChanged(name, oldMode, sel);
            SliceMsg(sel == 0 ? "核心规则已关：" + name + ".exe（已比较还原）"
                : "核心规则：" + name + ".exe → " + (sel == 1 ? "前台进程·前台区" : "后台进程·隔离区") + "，启动自动生效");
            SyncNameCombo(name, 3, sel);
        };

        fcCombo.SelectionChanged += (ss, ee) =>
        {
            if (_populating || _syncCb) return;
            int sel = fcCombo.SelectedIndex;
            if (sel < 0) return;
            if (sel == 0)
            {
                lock (Cfg.FcRules) Cfg.FcRules.Remove(name);
                Cfg.DeleteKey("FC_" + name);
                FirstCore.RuleRemoved(name);
                SliceMsg("首核调度已关：" + name + ".exe");
            }
            else
            {
                int core = fcCpus[sel - 1];
                int fcPrev;
                lock (Cfg.FcRules) if (!Cfg.FcRules.TryGetValue(name, out fcPrev)) fcPrev = -1;
                bool changed = fcPrev >= 0 && fcPrev != core;
                lock (Cfg.FcRules) Cfg.FcRules[name] = core;
                Cfg.SaveKey("FC_" + name, core.ToString());
                if (changed) FirstCore.RuleChanged(name, core);
                else FirstCore.RuleAdded(name, core);
                SliceMsg("首核调度：" + name + ".exe → " + core + "，启动自动生效");
            }
            SyncNameCombo(name, 4, sel);
        };

        procList.Items.Add(row);
    }

    /* ---------------- 下拉防滚轮误触（09-21，用户拍板） ----------------
     * WPF 下拉框鼠标悬停即响应滚轮：列表 200 行 × 多下拉，滚列表时极易静默改档；
     * 改档即记忆后误触=直接写持久规则。这里把滚轮转发给外层容器——列表照常滚动、值不变。
     * 展开下拉时不拦（用户就是在滚选项列表）。 */
    static void NoWheelScroll(ComboBox cb)
    {
        cb.PreviewMouseWheel += delegate(object ss, MouseWheelEventArgs ee)
        {
            if (ee.Handled || cb.IsDropDownOpen) return;
            ee.Handled = true;
            var fe = cb as FrameworkElement;
            var parent = fe != null ? fe.Parent as UIElement : null;
            if (parent == null) return;
            var fwd = new MouseWheelEventArgs(ee.MouseDevice, ee.Timestamp, ee.Delta);
            fwd.RoutedEvent = UIElement.MouseWheelEvent;
            fwd.Source = cb;
            parent.RaiseEvent(fwd);
        };
    }

    /* ---------------- 同名行状态同步（09-11 六控件：规则名字级，同名多实例各行的显示必须一致） ---------------- */
    static T FindInCol<T>(Grid g, int col) where T : class
    {
        foreach (var c in g.Children)
        {
            if (Grid.GetColumn((UIElement)c) != col) continue;
            var t = c as T;
            if (t != null) return t;
            var w = c as Grid;   // 列7 线程档=Grid 包装（tpCell），解一层
            if (w != null && w.Children.Count > 0) return w.Children[0] as T;
        }
        return null;
    }

    // 星标类（★/◆）同步：TextBlock 文本+颜色
    void SyncNameText(string name, int col, string onText, string offText, bool on)
    {
        foreach (var item in procList.Items)
        {
            var g = item as Grid;
            if (g == null || g.Tag as string != name) continue;
            var tb = FindInCol<TextBlock>(g, col);
            if (tb != null) { tb.Text = on ? onText : offText; tb.Foreground = Brush(on ? "#111111" : "#888888"); }
        }
    }

    // 下拉类同步：SelectedIndex 对齐（_syncCb 挡递归）
    void SyncNameCombo(string name, int col, int selIdx)
    {
        _syncCb = true;
        try
        {
            foreach (var item in procList.Items)
            {
                var g = item as Grid;
                if (g == null || g.Tag as string != name) continue;
                var cb = FindInCol<ComboBox>(g, col);
                if (cb != null && cb.SelectedIndex != selIdx) cb.SelectedIndex = selIdx;
            }
        }
        finally { _syncCb = false; }
    }

    /* ---------------- 核心隔离 UI（页3 顶部） ---------------- */
    void BuildIsoPanel()
    {
        if (lblIsoState == null) return;
        _isoStatusHandler = s => Ui(() => { if (lblIsoState != null) lblIsoState.Text = s; });
        Iso.StatusChanged += _isoStatusHandler;
        lblIsoState.Text = Iso.Status;
        BuildIsoModeCombo();
        RebuildIsoCoreRows();

        // 中断隔离区：标题行=标签+落点设置入口（文字链接式，与实心设备芯片视觉区分，防误认成设备开关）；
        // 芯片行=设备开关，点击把中断/DPC 钉到落点（注册表一次写入，重启生效）
        _irqChips.Clear();
        var irqHead = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, 6, 0, 8) };   // 底部 8：落点文字与芯片行拉开
        irqHead.Children.Add(new TextBlock
        {
            Text = "设备中断隔离", Foreground = Brush("#666666"), FontSize = 10,
            Width = 140, VerticalAlignment = VerticalAlignment.Center   // 同 CCD 行：⚙ 落点与核心格子列对齐
        });
        var irqMaskBtn = new Border
        {
            Cursor = Cursors.Hand, Background = Brushes.Transparent,
            VerticalAlignment = VerticalAlignment.Center
        };
        irqMaskBtn.Child = new TextBlock { FontSize = 10 };
        irqMaskBtn.ToolTip = "设置设备中断/DPC 的落点核心（这是设置入口，不是设备开关）\n跟随隔离区=与核心隔离同区；自定义=独立选核心，点下方设备芯片写入";
        irqMaskBtn.MouseLeftButtonUp += (s, e) => ShowIrqMaskWindow();
        irqMaskBtn.MouseEnter += (s, e) => ((TextBlock)irqMaskBtn.Child).Foreground = Brush("#111111");
        irqMaskBtn.MouseLeave += (s, e) => UpdateIrqMaskBtn();
        _irqMaskBtn = irqMaskBtn;
        UpdateIrqMaskBtn();
        irqHead.Children.Add(irqMaskBtn);
        isoCcdHost.Children.Add(irqHead);
        var irqRow = new WrapPanel();   // 标签已上标题行，芯片直接左排（不缩进，左侧不留空位）
        ulong irqMask = IrqIso.EffectiveMask();
        foreach (var d in IrqIso.EnumDevices(irqMask))
        {
            var chip = new Border
            {
                CornerRadius = new CornerRadius(4), Margin = new Thickness(0, 0, 4, 2),
                Padding = new Thickness(8, 2, 8, 2), Cursor = Cursors.Hand,
                ToolTip = d.FullName + "\nMSI: " + (d.Msi == 1 ? "开" : (d.Msi == 0 ? "关（线中断，无法钉核）" : "未知"))
                          + (d.Hosts.Length > 0 ? "\n挂载设备: " + d.Hosts + "（钉隔离区后其输入中断跨 CCD）" : "")
                          + (d.Custom ? "\n注意：中断已被第三方指定到其他核心" : "")
            };
            chip.Child = new TextBlock { Text = d.Label, FontSize = 9, HorizontalAlignment = HorizontalAlignment.Center };
            chip.Tag = d;
            StyleIrqChip(chip, d);
            chip.MouseLeftButtonUp += (s, e) => ToggleIrq(chip);
            _irqChips.Add(chip);
            irqRow.Children.Add(chip);
        }
        isoCcdHost.Children.Add(irqRow);
    }

    /* ---- 模式切换：硬隔离 / 软隔离（09-11 用户定稿） ---- */
    // 软隔离=SetProcessDefaultCpuSets 软引导：两区独立选核可重叠，负载高时可溢出，更温和
    // 模式切换=下拉框（与核心格子方块视觉区分，09-11 用户定稿）；先设值后挂事件，构建不触发切换
    void BuildIsoModeCombo()
    {
        isoModeHost.Children.Clear();
        var combo = new ComboBox
        {
            Style = win != null ? (Style)win.FindResource("SliceCombo") : null,
            Width = 96,
            FontSize = 11,
            VerticalAlignment = VerticalAlignment.Center,
            ToolTip = "隔离模式：\n硬隔离=进程亲和硬钉（游戏钉死前台区、其余进程钉死隔离区，不可越界；隔离区=勾选核心，前台区=其余）\n软隔离=CPU Sets 软引导（前台区/隔离区独立选核可重叠，进程被引导至对应区，负载高时允许溢出；更温和、对反作弊干扰小）"
        };
        combo.Items.Add("硬隔离");
        combo.Items.Add("软隔离");
        combo.SelectedIndex = Cfg.IsoSoft == 1 ? 1 : 0;
        NoWheelScroll(combo);
        combo.SelectionChanged += (s, e) =>
        {
            int sel = combo.SelectedIndex;
            if (sel < 0) return;
            SetIsoMode(sel);   // 0=硬 1=软
        };
        isoModeHost.Children.Add(combo);
        _isoModeCombo = combo;
    }

    void SetIsoMode(int soft)
    {
        if (Cfg.IsoSoft == soft) return;
        ulong oldIso, oldGame;
        Iso.Zones(out oldIso, out oldGame);
        Cfg.IsoSoft = soft;
        Cfg.SaveKey("ISO_MODE", soft == 1 ? "soft" : "hard");
        bool defaulted = soft == 1 && Iso.EnsureSoftDefaults();   // 首次切软隔离：空掩码默认全勾（两区可重叠）
        RebuildIsoCoreRows();
        FollowIsoSelf();       // 自身跟随新隔离区
        Iso.MaskChanged();     // 生效中：按旧模式还原→新模式重新生效
        ulong newIso, newGame;
        Iso.Zones(out newIso, out newGame);
        if (Cfg.IrqMode != "custom" && !defaulted) IrqIso.Resync(oldIso, newIso);   // 仅 follow 模式联动中断设备；默认全勾非用户选核，中断落点保持原样
        ulong irqNow = IrqIso.EffectiveMask();
        foreach (var chip in _irqChips) { var d = (IrqIso.Dev)chip.Tag; IrqIso.Refresh(d, irqNow); StyleIrqChip(chip, d); }
        RefillProcs();         // 首核下拉项按新前台区过滤
    }

    /* ---- 核心格子行（硬=CCD 行 / 软=区切换按钮+CCD 行；模式切换只重建这里，中断区不动） ---- */
    void RebuildIsoCoreRows()
    {
        isoCoreHost.Children.Clear();
        _isoBoxes.Clear();
        _softBoxes.Clear();
        _softZoneTabGame = _softZoneTabIso = null;
        if (!Topo.Supported)
        {
            isoCoreHost.Children.Add(new TextBlock
            {
                Text = "核心拓扑检测失败（或不支持 >64 逻辑处理器），隔离功能不可用",
                Foreground = Brush("#888888"), FontSize = 10, Margin = new Thickness(0, 4, 0, 4)
            });
            return;
        }
        if (Cfg.IsoSoft == 1) BuildSoftRows();
        else BuildHardRows();
    }

    void BuildHardRows()
    {
        BuildCcdRows(Cfg.IsoMask & Topo.AllMask, _isoBoxes, ToggleIsoCore);
    }

    // CCD 分行核心格子（硬/软共用：软隔离按当前编辑区掩码显示——单按钮切区，CCD 排版不变，双 CCD 不超宽）
    void BuildCcdRows(ulong mask, List<Border> boxes, Action<int> toggle)
    {
        for (int c = 0; c < Topo.Ccds.Count; c++)
        {
            var row = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, 3, 0, 3) };
            row.Children.Add(new TextBlock
            {
                Text = Topo.CcdLabel(c), Foreground = Brush("#666666"), FontSize = 10,
                Width = 140, VerticalAlignment = VerticalAlignment.Center   // 140：长标签（CCD0·L3 96MB·3D缓存）不贴 C0
            });
            for (int i = 0; i < Topo.Cores.Count; i++)
            {
                if (Topo.Cores[i].Ccd != c) continue;
                int idx = i;
                var box = new Border
                {
                    Width = 30, Height = 20, CornerRadius = new CornerRadius(4),
                    Margin = new Thickness(0, 0, 4, 0), Cursor = Cursors.Hand,
                    ToolTip = CoreTip(idx)
                };
                box.Child = new TextBlock
                {
                    Text = "C" + idx, FontSize = 9,
                    HorizontalAlignment = HorizontalAlignment.Center,
                    VerticalAlignment = VerticalAlignment.Center
                };
                StyleIsoBox(box, (mask & Topo.Cores[idx].Mask) != 0);
                box.MouseLeftButtonUp += (s, e) => toggle(idx);
                while (boxes.Count <= idx) boxes.Add(null);
                boxes[idx] = box;
                row.Children.Add(box);
            }
            isoCoreHost.Children.Add(row);
        }
    }

    // 软隔离：区切换文字 tab（前台区/隔离区，当前区白字+下划线）+ CCD 分行（与硬隔离同排版，双 CCD 不超宽；两区独立可重叠）
    void BuildSoftRows()
    {
        var head = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, 3, 0, 3) };
        head.Children.Add(new TextBlock
        {
            Text = "编辑区", Foreground = Brush("#666666"), FontSize = 10,
            Width = 140, VerticalAlignment = VerticalAlignment.Center
        });
        _softZoneTabGame = MakeZoneTab("前台区", 0);
        _softZoneTabIso = MakeZoneTab("隔离区", 1);
        head.Children.Add(_softZoneTabGame);
        head.Children.Add(_softZoneTabIso);
        StyleZoneTabs();
        isoCoreHost.Children.Add(head);
        BuildCcdRows(SoftZoneMask(), _softBoxes, ToggleSoftZoneCore);
    }

    TextBlock MakeZoneTab(string text, int zone)
    {
        var tb = new TextBlock
        {
            Text = text, FontSize = 10,
            Margin = new Thickness(zone == 1 ? 18 : 0, 0, 0, 0),
            Cursor = Cursors.Hand,
            ToolTip = "点击切换编辑前台区 / 隔离区（两区独立勾选，可重叠）\n前台规则进程引导至前台区，后台规则与普通进程收拢至隔离区"
        };
        tb.MouseLeftButtonUp += (s, e) =>
        {
            if (_softEditZone != zone) { _softEditZone = zone; RebuildIsoCoreRows(); }
            e.Handled = true;
        };
        tb.MouseEnter += (s, e) => { if (_softEditZone != zone) tb.Foreground = Brush("#666666"); };
        tb.MouseLeave += (s, e) => StyleZoneTabs();
        return tb;
    }

    void StyleZoneTabs()
    {
        if (_softZoneTabGame == null) return;
        bool game = _softEditZone == 0;
        _softZoneTabGame.Foreground = Brush(game ? "#111111" : "#888888");
        _softZoneTabIso.Foreground = Brush(game ? "#888888" : "#111111");
        _softZoneTabGame.TextDecorations = game ? TextDecorations.Underline : null;
        _softZoneTabIso.TextDecorations = game ? null : TextDecorations.Underline;
    }

    ulong SoftZoneMask()
    {
        return _softEditZone == 1 ? Cfg.SoftIsoMask & Topo.AllMask : Cfg.SoftGameMask & Topo.AllMask;
    }

    void ToggleSoftZoneCore(int idx)
    {
        if (_softEditZone == 1) ToggleSoftIsoCore(idx);
        else ToggleSoftGameCore(idx);
    }

    void ToggleSoftGameCore(int idx)
    {
        ulong m = Topo.Cores[idx].Mask;
        ulong prev = Cfg.SoftGameMask & Topo.AllMask;
        ulong next = prev ^ m;
        if ((next & m) == 0 && next == 0)   // 本次是取消勾选且前台区将空
        {
            Iso.SetStatus("不能取消全部勾选：前台区至少保留一个核心");
            return;
        }
        Cfg.SoftGameMask = next;
        Cfg.SaveKey("ISO_SOFT_GAME", next.ToString("X"));
        RefreshSoftBoxes();
        Iso.MaskChanged();
        RefillProcs();   // 首核下拉项按新前台区过滤
    }

    void ToggleSoftIsoCore(int idx)
    {
        ulong m = Topo.Cores[idx].Mask;
        ulong prev = Cfg.SoftIsoMask & Topo.AllMask;
        ulong next = prev ^ m;
        if ((next & m) == 0 && next == 0)   // 本次是取消勾选且隔离区将空
        {
            Iso.SetStatus("不能取消全部勾选：隔离区至少保留一个核心");
            return;
        }
        Cfg.SoftIsoMask = next;
        Cfg.SaveKey("ISO_SOFT_ISO", next.ToString("X"));
        RefreshSoftBoxes();
        Iso.MaskChanged();
        FollowIsoSelf();   // 自身跟随新隔离区
        if (Cfg.IrqMode != "custom") IrqIso.Resync(prev, next);   // 仅 follow 模式联动中断设备
        ulong irqNow = IrqIso.EffectiveMask();
        foreach (var chip in _irqChips) { var d = (IrqIso.Dev)chip.Tag; IrqIso.Refresh(d, irqNow); StyleIrqChip(chip, d); }
    }

    void RefreshSoftBoxes()
    {
        ulong m = SoftZoneMask();
        for (int i = 0; i < _softBoxes.Count; i++)
            if (_softBoxes[i] != null) StyleIsoBox(_softBoxes[i], (m & Topo.Cores[i].Mask) != 0);
    }

    // 落点设置入口的文字/颜色刷新（BuildIsoPanel 构建、小窗 apply、hover 离开三处调用）
    void UpdateIrqMaskBtn()
    {
        if (_irqMaskBtn == null) return;
        var tb = (TextBlock)_irqMaskBtn.Child;
        if (Cfg.IrqMode == "custom")
        {
            tb.Text = "⚙ 中断落点：自定义 " + IrqCoresText(Cfg.IrqMask & Topo.AllMask);
            tb.Foreground = Brush("#111111");
        }
        else
        {
            tb.Text = "⚙ 中断落点：跟随隔离区";
            tb.Foreground = Brush("#666666");
        }
    }

    // 掩码→核心名列表（整核 SMT 对都在掩码里才算）：0xF000 → "C6,C7"
    static string IrqCoresText(ulong mask)
    {
        var names = new List<string>();
        if (Topo.Supported)
            for (int i = 0; i < Topo.Cores.Count; i++)
                if ((mask & Topo.Cores[i].Mask) == Topo.Cores[i].Mask) names.Add("C" + i);
        return names.Count == 0 ? "?" : string.Join(",", names.ToArray());
    }

    static void StyleIrqChip(Border chip, IrqIso.Dev d)
    {
        chip.Background = Brush(d.Isolated ? "#111111" : "#FFFFFF");
        chip.BorderBrush = Brush(d.Isolated ? "#111111" : (d.Custom ? "#888888" : "#D0D0D0"));
        chip.BorderThickness = new Thickness(1);
        ((TextBlock)chip.Child).Foreground = Brush(d.Isolated ? "#FFFFFF" : "#666666");
    }

    void ToggleIrq(Border chip)
    {
        var d = (IrqIso.Dev)chip.Tag;
        ulong irq = IrqIso.EffectiveMask();
        string r = IrqIso.SetIsolated(d, !d.Isolated, irq);
        IrqIso.Refresh(d, irq);
        StyleIrqChip(chip, d);
        if (d.Isolated && d.Hosts.Length > 0)
            r += "（该控制器挂着 " + d.Hosts + "，输入中断将跨 CCD，手感敏感不建议）";
        Iso.SetStatus(r);
    }

    static string CoreTip(int idx)
    {
        ulong m = Topo.Cores[idx].Mask;
        var cpus = new List<int>();
        for (int b = 0; b < 64; b++) if ((m & (1UL << b)) != 0) cpus.Add(b);
        string tip = "核心 " + idx + "（CPU " + string.Join(",", cpus) + "）";
        if (Topo.Hybrid) tip += Topo.Ccds[Topo.Cores[idx].Ccd].IsP ? " · P核" : " · E核";
        return tip;
    }

    static void StyleIsoBox(Border box, bool on)
    {
        box.Background = Brush(on ? "#111111" : "#FFFFFF");
        box.BorderBrush = Brush(on ? "#111111" : "#D0D0D0");
        box.BorderThickness = new Thickness(1);
        ((TextBlock)box.Child).Foreground = Brush(on ? "#FFFFFF" : "#666666");
    }

    void RefreshIsoBoxes()
    {
        ulong mask = Cfg.IsoMask & Topo.AllMask;
        for (int i = 0; i < _isoBoxes.Count; i++)
            if (_isoBoxes[i] != null) StyleIsoBox(_isoBoxes[i], (mask & Topo.Cores[i].Mask) != 0);
    }

    // 自身亲和跟随当前模式隔离区并排除中断落点（2026-08-18 用户：RealTime+全核的周期 tick 落到 CCD0 抢游戏线程→手感周期慢一拍）
    // 隔离规则引擎本就豁免自身，所以这里手动钉；隔离关着时回全核。
    // 中断亲和=DPC 落点，自身 UI/心跳线程不能与之抢核（10-06：本机 IRQ_MODE=custom、IRQ_MASK=3，全部设备中断落核 0/1，自身亲和含 0/1 → 动效卡顿根因）
    static void FollowIsoSelf()
    {
        try
        {
            Topo.Detect();
            ulong iso, game;
            Iso.Zones(out iso, out game);
            ulong self = iso != 0 ? iso : Topo.AllMask;
            ulong irq = IrqIso.EffectiveMask();
            if (irq != 0 && (self & ~irq) != 0) self &= ~irq;   // 排除中断落点，但至少要给自身留一个核
            Native.SetProcessAffinityMask(Native.GetCurrentProcess(), (UIntPtr)self);
        }
        catch { }
    }

    void ToggleIsoCore(int idx)
    {
        ulong coreMask = Topo.Cores[idx].Mask;
        ulong prev = Cfg.IsoMask & Topo.AllMask;
        ulong next = prev ^ coreMask;
        if ((next & coreMask) != 0 && next == Topo.AllMask)   // 本次是勾选且导致全选 → 前台区为空，拒绝
        {
            Iso.SetStatus("不能全部勾选：前台区至少保留一个核心");
            return;
        }
        Cfg.IsoMask = next;
        Cfg.SaveKey("ISO_MASK", next.ToString("X"));
        RefreshIsoBoxes();
        Iso.MaskChanged();
        FollowIsoSelf();   // 自身跟随新隔离区
        // 仅 follow 模式联动中断设备；custom 是用户显式钉的不动
        if (Cfg.IrqMode != "custom") IrqIso.Resync(prev, next);
        ulong irqNow = IrqIso.EffectiveMask();
        foreach (var chip in _irqChips) { var d = (IrqIso.Dev)chip.Tag; IrqIso.Refresh(d, irqNow); StyleIrqChip(chip, d); }
        RefillProcs();   // 首核下拉项按新前台区过滤（列表为空时内部直接返回）
    }

    /* ---------------- 中断落点选择小窗（设备中断隔离标题行「⚙ 中断落点」入口） ---------------- */
    // 两模式：follow=跟随隔离区（默认）/ custom=自定义核心。即改即存：已隔离设备立即重写到新落点
    //（IrqIso.Resync，第三方掩码不动），重启后生效；至少留 1 核，选前台区核心只提示不禁止；
    // 切模式不清 IRQ_MASK，切回 custom 掩码记忆。
    void ShowIrqMaskWindow()
    {
        if (!Topo.Supported) return;
        var win = new Window
        {
            Width = 500, SizeToContent = SizeToContent.Height,
            WindowStyle = WindowStyle.None, AllowsTransparency = true, Background = Brushes.Transparent,
            ResizeMode = ResizeMode.NoResize, WindowStartupLocation = WindowStartupLocation.CenterOwner,
            Owner = Window.GetWindow(isoCcdHost)
        };
        var root = new Border { CornerRadius = new CornerRadius(12), BorderBrush = Brush("#E3E3E3"), BorderThickness = new Thickness(1) };
        root.Background = new LinearGradientBrush(
            new GradientStopCollection {
                new GradientStop(Color.FromRgb(0xFA, 0xFA, 0xFA), 0),
                new GradientStop(Color.FromRgb(0xFF, 0xFF, 0xFF), 0.55),
                new GradientStop(Color.FromRgb(0xFA, 0xFA, 0xFA), 1) },
            new Point(0, 0), new Point(1, 1));
        var panel = new StackPanel { Margin = new Thickness(18, 14, 18, 16) };
        root.Child = panel;
        win.Content = root;

        var head = new Grid();
        head.Children.Add(new TextBlock { Text = "中断落点核心", FontSize = 13, Foreground = Brush("#111111") });
        // × 用 Border 包装加大点击面；MouseLeftButtonDown 直接关闭+Handled——挂 Up 会被标题栏 DragMove 吞掉
        var xBtn = new Border
        {
            Padding = new Thickness(10, 0, 0, 6), Background = Brushes.Transparent,
            Cursor = Cursors.Hand, HorizontalAlignment = HorizontalAlignment.Right,
            VerticalAlignment = VerticalAlignment.Top
        };
        xBtn.Child = new TextBlock { Text = "×", FontSize = 16, Foreground = Brush("#666666") };
        xBtn.MouseLeftButtonDown += (s, e) => { e.Handled = true; win.Close(); };
        head.Children.Add(xBtn);
        head.MouseLeftButtonDown += (s, e) => win.DragMove();   // 只标题栏可拖（挂 root 会让点格子变拖窗）
        panel.Children.Add(head);
        panel.Children.Add(new TextBlock
        {
            Text = "设备中断/DPC 落点。跟随隔离区=与核心隔离同区；自定义=独立选择。\n切换落点时已隔离设备立即重写（重启后生效），第三方指定掩码的设备不动。",
            FontSize = 10, Foreground = Brush("#666666"), TextWrapping = TextWrapping.Wrap, Margin = new Thickness(0, 8, 0, 10)
        });

        // 模式块（风格同中断芯片）
        var modeRow = new StackPanel { Orientation = Orientation.Horizontal };
        Func<string, Border> makeModeBtn = text =>
        {
            var b = new Border
            {
                CornerRadius = new CornerRadius(4), Margin = new Thickness(0, 0, 6, 0),
                Padding = new Thickness(10, 3, 10, 3), Cursor = Cursors.Hand, BorderThickness = new Thickness(1)
            };
            b.Child = new TextBlock { Text = text, FontSize = 10 };
            return b;
        };
        var modeFollow = makeModeBtn("跟随隔离区");
        var modeCustom = makeModeBtn("自定义");
        modeRow.Children.Add(modeFollow);
        modeRow.Children.Add(modeCustom);
        panel.Children.Add(modeRow);

        // 核心格子区（CCD 分行，同 BuildIsoPanel 结构）
        var coreHost = new StackPanel { Margin = new Thickness(0, 8, 0, 0) };
        panel.Children.Add(coreHost);
        var status = new TextBlock
        {
            FontSize = 10, Foreground = Brush("#666666"), TextWrapping = TextWrapping.Wrap,
            Margin = new Thickness(0, 10, 0, 0)
        };
        panel.Children.Add(status);

        string mode = Cfg.IrqMode == "custom" ? "custom" : "follow";
        ulong curIso, curGame;
        Iso.Zones(out curIso, out curGame);   // 当前模式隔离区
        ulong sel = (Cfg.IrqMask != 0 ? Cfg.IrqMask : curIso) & Topo.AllMask;   // 有记忆掩码用记忆，否则预填隔离区
        var boxes = new List<Border>();

        Action<Border, bool> styleMode = (b, on) =>
        {
            b.Background = Brush(on ? "#111111" : "#FFFFFF");
            b.BorderBrush = Brush(on ? "#111111" : "#D0D0D0");
            ((TextBlock)b.Child).Foreground = Brush(on ? "#FFFFFF" : "#666666");
        };
        Action refresh = null, apply = null;
        refresh = () =>
        {
            styleMode(modeFollow, mode == "follow");
            styleMode(modeCustom, mode == "custom");
            bool edit = mode == "custom";
            ulong eff = edit ? sel : curIso;
            for (int i = 0; i < boxes.Count; i++)
                if (boxes[i] != null)
                {
                    StyleIsoBox(boxes[i], (sel & Topo.Cores[i].Mask) != 0);
                    boxes[i].Opacity = edit ? 1.0 : 0.35;   // 非自定义模式格子只读预览
                }
            int n = 0;
            for (int b = 0; b < 64; b++) if ((eff & (1UL << b)) != 0) n++;
            bool warn = edit && (sel & ~curIso) != 0;   // 选中核落在隔离区外=前台区（软隔离两区可重叠，此提示为保守提示）
            status.Text = "生效落点 0x" + eff.ToString("X") + "（" + n + " 个逻辑 CPU）" + (edit ? "" : " · 跟随隔离区")
                        + (warn ? "　⚠ 含前台区核心，中断可能干扰游戏线程" : "");
            status.Foreground = Brush(warn ? "#111111" : "#666666");
        };
        apply = () =>
        {
            ulong oldEff = IrqIso.EffectiveMask();
            Cfg.IrqMode = mode;
            if (mode == "custom") Cfg.IrqMask = sel;
            Cfg.SaveKey("IRQ_MODE", mode);
            Cfg.SaveKey("IRQ_MASK", Cfg.IrqMask.ToString("X"));
            ulong newEff = IrqIso.EffectiveMask();
            IrqIso.Resync(oldEff, newEff);
            foreach (var chip in _irqChips) { var d = (IrqIso.Dev)chip.Tag; IrqIso.Refresh(d, newEff); StyleIrqChip(chip, d); }
            UpdateIrqMaskBtn();
            refresh();
        };
        for (int c = 0; c < Topo.Ccds.Count; c++)
        {
            var row = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, 3, 0, 3) };
            row.Children.Add(new TextBlock
            {
                Text = Topo.CcdLabel(c), Foreground = Brush("#666666"), FontSize = 10,
                Width = 140, VerticalAlignment = VerticalAlignment.Center   // 同主窗：长标签不贴格子
            });
            for (int i = 0; i < Topo.Cores.Count; i++)
            {
                if (Topo.Cores[i].Ccd != c) continue;
                int idx = i;
                var box = new Border
                {
                    Width = 30, Height = 20, CornerRadius = new CornerRadius(4),
                    Margin = new Thickness(0, 0, 4, 0), Cursor = Cursors.Hand, ToolTip = CoreTip(idx)
                };
                box.Child = new TextBlock
                {
                    Text = "C" + idx, FontSize = 9,
                    HorizontalAlignment = HorizontalAlignment.Center,
                    VerticalAlignment = VerticalAlignment.Center
                };
                box.MouseLeftButtonUp += (s, e) =>
                {
                    if (mode != "custom") return;   // 非自定义模式格子只读
                    ulong next = sel ^ Topo.Cores[idx].Mask;
                    if ((next & Topo.AllMask) == 0) { Iso.SetStatus("中断落点至少保留一个核心"); return; }
                    sel = next;
                    apply();
                };
                while (boxes.Count <= idx) boxes.Add(null);
                boxes[idx] = box;
                row.Children.Add(box);
            }
            coreHost.Children.Add(row);
        }
        modeFollow.MouseLeftButtonUp += (s, e) => { if (mode == "follow") return; mode = "follow"; apply(); };
        modeCustom.MouseLeftButtonUp += (s, e) =>
        {
            if (mode == "custom") return;
            mode = "custom";
            if ((sel & Topo.AllMask) == 0) sel = Topo.AllMask & (ulong)(-(long)Topo.AllMask);   // 无隔离区时预填最低核
            apply();
        };
        win.KeyDown += (s, e) => { if (e.Key == Key.Escape) win.Close(); };
        refresh();
        win.ShowDialog();
    }

    /* ---------------- 待机内存模块 ---------------- */
    const int MEMLIST_CLASS = 80, CMD_PURGE_STANDBY = 4, CMD_PURGE_STANDBY_LOW = 5;   // 5=只清低优先级(P0-3) standby：游戏降级页在 P5 碰不到（20348 实测）

    public static void EnablePrivilege(string name)
    {
        try
        {
            IntPtr tok;
            if (!Native.OpenProcessToken(Native.GetCurrentProcess(), 0x28, out tok)) return;   // ADJUST_PRIVILEGES|QUERY
            long luid;
            if (Native.LookupPrivilegeValue(null, name, out luid))
            {
                var tp = new Native.TOKEN_PRIVILEGES { Count = 1, LuidLow = (int)(luid & 0xFFFFFFFF), LuidHigh = (int)(luid >> 32), Attr = 2 };
                Native.AdjustTokenPrivileges(tok, false, ref tp, 0, IntPtr.Zero, IntPtr.Zero);
            }
            Native.CloseHandle(tok);
        }
        catch { }
    }

    // lowOnly=true 只清低优先级 standby（智能清理在设定进程在跑时走这条路）：游戏切后台降级的页
    // 是高优先级 P5，全力清会把它们抹掉→切回游戏全变硬缺页狂卡（2026-08-31 用户报障定位）。
    // fail-safe：低优先命令不可用的系统上返回 false 报错即可，绝不偷偷回退全力清。
    static bool PurgeStandby(bool lowOnly)
    {
        EnablePrivilege("SeDebugPrivilege");
        EnablePrivilege("SeProfileSingleProcessPrivilege");
        int cmd = lowOnly ? CMD_PURGE_STANDBY_LOW : CMD_PURGE_STANDBY;
        return Native.NtSetSystemInformation(MEMLIST_CLASS, ref cmd, 4) == 0;
    }

    // 读数：NtQuerySystemInformation(80) 偏移 5..12 PageCountByPriority[8]×4096（不走 PDH）
    static double ReadStandbyMB()
    {
        for (int size = 256; size <= 1024; size *= 2)
        {
            IntPtr p = Marshal.AllocHGlobal(size);
            try
            {
                int ret;
                int st = Native.NtQuerySystemInformation(MEMLIST_CLASS, p, size, out ret);
                if (st == 0)
                {
                    long pages = 0;
                    for (int i = 0; i < 8; i++)
                        pages += Marshal.ReadInt64(p, IntPtr.Size * (5 + i));
                    return pages * 4096.0 / 1048576.0;
                }
                if (st != unchecked((int)0xC0000004)) break;
            }
            finally { Marshal.FreeHGlobal(p); }
        }
        return -1;
    }

    void RefreshMemStats()
    {
        if (standbyNum == null) return;
        double sb = ReadStandbyMB();
        standbyNum.Text = sb >= 0 ? sb.ToString("#,0") : "—";
        try
        {
            Native.PERF_INFO pi; pi.cb = Marshal.SizeOf(typeof(Native.PERF_INFO));
            if (Native.GetPerformanceInfo(out pi, pi.cb))
            {
                long page = pi.PageSize.ToInt64();
                double total = pi.PhysicalTotal.ToInt64() * page / 1073741824.0;
                double avail = pi.PhysicalAvailable.ToInt64() * page / 1073741824.0;
                memInfo.Text = string.Format("物理 {0:0.#} GB · 可用 {1:0.#} GB", total, avail);
                double ratio = (total > 0 && sb >= 0) ? (sb / 1024.0) / total : 0;
                memRatioText.Text = "待机占物理内存 " + (ratio * 100).ToString("0") + "%";
                memRatioBar.Width = Math.Max(2, Math.Min(180, ratio * 180));
            }
        }
        catch { }
    }

    void DoPurge(string source, bool lowOnly)
    {
        double before = ReadStandbyMB();
        bool ok = PurgeStandby(lowOnly);
        Thread.Sleep(500);
        double after = ReadStandbyMB();
        string msg;
        if (!ok) msg = source + (lowOnly ? " · 低优先清理不可用（本系统不支持）" : " · 清理失败（需管理员权限）");
        else if (before >= 0 && after >= 0) msg = string.Format("{0} · 释放 {1:0} MB · {2:HH:mm:ss}", source, Math.Max(0, before - after), DateTime.Now);
        else msg = string.Format("{0} · 完成 · {1:HH:mm:ss}", source, DateTime.Now);
        lastPurgeMsg = "最近清理：" + msg;
        SetTrayTip("DunSuiteLite · " + msg);   // 窗口关着也能从托盘提示确认清过
        Ui(() =>
        {
            lblLastPurge.Text = lastPurgeMsg;
            RefreshMemStats();
        });
    }

    void SetTrayTip(string tip)
    {
        var nid = new NID { cbSize = Marshal.SizeOf(typeof(NID)), hWnd = msgHwnd, uID = 1, uFlags = NIF_TIP, szTip = tip };
        Shell_NotifyIconW(NIM_MODIFY, ref nid);
    }

    // 事件线程（事件模式专属，纯等待零轮询）
    void MemEventLoop()
    {
        IntPtr h = Native.CreateMemoryResourceNotification(0);
        if (h == IntPtr.Zero) return;
        while (running)
        {
            Native.WaitForSingleObject(h, 0xFFFFFFFF);
            if (!running) break;
            if (memMode == "event")
            {
                double sb = ReadStandbyMB();
                if (sb < 0 || sb >= thresholdMB) DoPurge("事件", false);
            }
        }
        Native.CloseHandle(h);
    }

    // 定时模式专属 Timer（阈值模式已改事件驱动：Shell Hook 窗口创建 + TrayTrim 兜底，无轮询）
    void ApplyMemMode()
    {
        try { if (memTickTimer != null) { memTickTimer.Dispose(); memTickTimer = null; } } catch { }
        if (memMode == "smart")
            CheckStandbyThreshold();   // 进模式/启动立即首查；之后由事件驱动
        else if (memMode == "timer")
            memTickTimer = new System.Threading.Timer(_ => DoPurge("定时", false), null, intervalMin * 60000, intervalMin * 60000);
    }

    DateTime _lastStdCheck;   // 跨线程读写的撕裂无害：最坏多查一次
    int _fgPurgePending;      // 前台游戏延迟清理排期标志（Interlocked，防叠排）
    const int FG_SETTLE_MS = 45000;   // 切进游戏后的沉降窗口：避开瞬时加载/降级页回填期
    readonly object _fgLock = new object();
    DateTime _fgGameSince = DateTime.MinValue;   // 前台是规则游戏的起始时刻（MinValue=前台非游戏/未知）
    string _fgGameName;   // 当前前台规则游戏进程名——游戏A直切游戏B也算"刚切进来"，要重置计时

    // "设定过的进程"名单（线程档/隔离游戏/首核/算法/时间片等——与页3"已配置"筛选同口径）
    static HashSet<string> GameRuleNames()
    {
        var names = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        lock (Cfg.SliceRules) foreach (var k in Cfg.SliceRules.Keys) names.Add(k);
        lock (Cfg.IsoGames) foreach (var n in Cfg.IsoGames) names.Add(n);
        lock (Cfg.FcRules) foreach (var k in Cfg.FcRules.Keys) names.Add(k);
        return names;
    }

    // 名单进程任一在跑？只在清理触发时快照一次进程列表，事件驱动零轮询。
    static bool GameRuleProcRunning(HashSet<string> names)
    {
        if (names.Count == 0) return false;
        foreach (var n in names)
            try { if (Process.GetProcessesByName(n).Length > 0) return true; } catch { }
        return false;
    }

    // 窗口句柄→进程名（取不到返回 null）
    static string ProcNameOfWindow(IntPtr h)
    {
        try
        {
            if (h == IntPtr.Zero) return null;
            uint pid;
            Native.GetWindowThreadProcessId(h, out pid);
            if (pid == 0) return null;
            using (Process p = Process.GetProcessById((int)pid)) return p.ProcessName;
        }
        catch { return null; }
    }

    // 前台窗口进程名（取不到返回 null）
    static string ForegroundProcName()
    {
        IntPtr h;
        try { h = Native.GetForegroundWindow(); } catch { return null; }
        return ProcNameOfWindow(h);
    }

    // Shell Hook 窗口激活事件（sc==4/0x8004，lParam=被激活窗口句柄）维护"前台游戏起始时刻"：
    // 切进游戏打点、切去非游戏清零——沉降延迟按这个时刻算剩余，坐稳的游戏不再白等。
    void NoteForegroundActive(IntPtr hwnd)
    {
        try
        {
            string fg = ProcNameOfWindow(hwnd);
            if (fg == null) fg = ForegroundProcName();   // 句柄失效兜底直读前台
            bool isGame = fg != null && GameRuleNames().Contains(fg);
            lock (_fgLock)
            {
                if (isGame)
                {
                    if (!string.Equals(_fgGameName, fg, StringComparison.OrdinalIgnoreCase))
                    {
                        _fgGameName = fg;
                        _fgGameSince = DateTime.Now;   // 前台游戏变了（含A直切B）→重新沉降
                    }
                }
                else { _fgGameName = null; _fgGameSince = DateTime.MinValue; }
            }
        }
        catch { }
    }

    // 智能清理（smart 模式专属）：系统没有"待机超阈值"事件（低内存通知在待机积压时永远不触发——
    // standby 计入可用内存），故挂到自有事件源：Shell Hook 窗口创建/窗口激活（用户活跃=检查密集=正是要内存的时刻）
    // + TrayTrim 10min 兜底（挂机期覆盖）。10s 去抖防窗口连发。
    // 分流判据（2026-09-01 重做，替代"游戏在跑=低优清"旧思路——低优清碰不到 P5 主体待机，游戏内等于不清）：
    //   无游戏在跑          → 立即全力清
    //   游戏在跑+前台是游戏 → 坐稳 FG_SETTLE_MS 后全力清（避开切进游戏瞬间的瞬时加载：此刻清会抹掉
    //                          正在回填的降级页→硬缺页狂卡；沉降后游戏活跃页已回工作集，清待机安全。
    //                          已坐稳超窗口的直接立即清，不白等）
    //   游戏在跑+前台非游戏 → 不清（游戏切后台的降级页在 P5 待机里，清了切回必卡——08-31 教训保留）
    void CheckStandbyThreshold()
    {
        try
        {
            if (memMode != "smart") return;
            if ((DateTime.Now - _lastStdCheck).TotalSeconds < 10) return;
            _lastStdCheck = DateTime.Now;
            double sb = ReadStandbyMB();
            if (sb < 0 || sb < thresholdMB) return;
            var names = GameRuleNames();
            // DoPurge 内含 Sleep(500) 前后对比采样——本方法会被 WndProc 消息线程（Shell Hook/激活事件）调用，
            // 必须扔后台线程，否则清理时卡消息循环 500ms（热键路径同款写法）
            if (!GameRuleProcRunning(names))
            {
                new Thread(() => DoPurge("智能", false)) { IsBackground = true }.Start();
                return;
            }
            string fg = ForegroundProcName();
            if (fg == null || !names.Contains(fg)) return;   // 游戏挂后台：保护它的待机页，不动
            // 前台是游戏：坐稳超沉降窗口（如长时间游戏后的 10min 兜底触发）→立即清；刚切进来→排延迟清
            DateTime since;
            lock (_fgLock)
            {
                if (_fgGameSince == DateTime.MinValue) { _fgGameSince = DateTime.Now; _fgGameName = fg; }   // 漏了激活事件的保守兜底：按"刚切进来"算
                since = _fgGameSince;
            }
            if ((DateTime.Now - since).TotalMilliseconds >= FG_SETTLE_MS)
                new Thread(() => DoPurge("智能·游戏前台", false)) { IsBackground = true }.Start();
            else
                ScheduleForegroundPurge();
        }
        catch { }
    }

    // 前台游戏延迟清理：睡到沉降点（_fgGameSince+FG_SETTLE_MS）再复核清理。
    // 睡到点醒来发现沉降期被"切走又切回"重置了→按新时刻继续睡（循环重算），不会在上一次回填窗口内误清。
    // 复核四条件（仍 smart/游戏仍在跑/前台仍是游戏/阈值仍超）失败静默放弃，等下一次事件再排——不追尾巴。
    void ScheduleForegroundPurge()
    {
        if (Interlocked.CompareExchange(ref _fgPurgePending, 1, 0) != 0) return;   // 已排期不叠加
        new Thread(() =>
        {
            try
            {
                for (;;)
                {
                    DateTime since;
                    lock (_fgLock) since = _fgGameSince;
                    if (since == DateTime.MinValue) return;   // 已切出游戏
                    int wait = (int)Math.Max(0, FG_SETTLE_MS - (DateTime.Now - since).TotalMilliseconds);
                    if (wait > 0) { Thread.Sleep(wait); continue; }
                    if (memMode != "smart") return;
                    var names = GameRuleNames();
                    if (!GameRuleProcRunning(names)) return;
                    string fg = ForegroundProcName();
                    if (fg == null || !names.Contains(fg)) return;   // 沉降点瞬间恰好切走→不清
                    double sb = ReadStandbyMB();
                    if (sb < 0 || sb < thresholdMB) return;
                    DoPurge("智能·游戏前台", false);
                    return;
                }
            }
            catch { }
            finally { Interlocked.Exchange(ref _fgPurgePending, 0); }
        }) { IsBackground = true }.Start();
    }

    void SetMemMode(string m)
    {
        memMode = m;
        RefreshPills();
        Cfg.SaveKey("Mode", m);
        ApplyMemMode();
    }

    void RefreshPills()
    {
        if (pillOff == null) return;
        StylePill(pillOff, memMode == "off");
        StylePill(pillSmart, memMode == "smart");
        StylePill(pillTimer, memMode == "timer");
    }

    void ApplyHotkey()
    {
        try { UnregisterHotKey(msgHwnd, HOTKEY_ID); } catch { }
        if (hotkeyEnabled) RegisterHotKey(msgHwnd, HOTKEY_ID, 0x2 | 0x4, 0x4D); // Ctrl+Shift+M
    }

    /* ---------------- 计时器模块：UI 桥接 ---------------- */
    // 引擎回调可能来自任意后台线程，且窗口可能已销毁——统一经 uiDisp 转发并判 win
    void Ui(Action a)
    {
        var d = uiDisp;
        if (d == null) return;   // 窗口从未打开：无可转达（各回调自带空判；托盘期反馈走托盘提示）
        try { d.BeginInvoke(new Action(() => { if (win != null) a(); })); } catch { }
    }

    // slept 持续监测（窗口开着才采样，关窗纯休眠）
    void StartMonitor()
    {
        _monThread = new Thread(() =>
        {
            while (_monRun)
            {
                if (_monPause) { _monWake.Wait(); continue; }   // 关窗：事件纯阻塞，零唤醒
                double s = _engine.SampleBurst();
                if (_monWarm > 0) { _monWarm--; Thread.Sleep(150); continue; }   // 预暖拍：采样照做（本身就是焐机）但不上屏
                Ui(() => SetSleptText(s));
                Thread.Sleep(1000);
            }
        });
        _monThread.IsBackground = true;
        _monThread.Start();
    }

    // ================= DPC =================
    int _dpcFail;
    bool _dpcReconnecting, _dpcStarting;
    // 2026-08-28 终版：自动判定全撤（探针/兜底经 22H2 实测证伪——GetTickCount64 在 22H2 不反映真实中断、
    // 用户态请求全平台全局有效，"后台掉 15ms"真凶是旧驱动退出写回旧值，Reassert 能治）。
    // 驱动改手动「内核解锁」开关：开=常驻（100s 间隔），关=开窗看图临时 1ms 随窗停。
    bool _dpcKeepAlive;
    bool _autoDriver;   // TimerDog 子进程探针判定全局无效后自动兜底拉起=常驻（与手动开关同等语义，只自动兜一次）

    static string FmtInterval(uint us)
    {
        double ms = us / 1000.0;
        if (ms < 1000) return ms.ToString("0.#") + "ms";
        double sec = ms / 1000;
        if (sec < 120) return sec.ToString("0.#") + "s";
        return (sec / 60).ToString("0.#") + "min";
    }

    string DpcStateText()
    {
        if (_dpc.Ok) return _dpc.StreamOffActive ? "运行中（零流解锁）" : "运行中（间隔 " + FmtInterval(_dpc.ActiveIntervalUs) + "）";
        return string.IsNullOrEmpty(_dpc.Error) ? ((_dpcKeepAlive || _autoDriver) ? "启动中…" : "未启用") : "不可用: " + _dpc.Error;
    }

    // observe=true=开窗观测档（1ms 精细采样）；false=常驻档（Cfg.DpcInterval，内核解锁开关语义）
    void StartDpc(bool observe)
    {
        if (_dpc.Ok || _dpcStarting) return;   // 防 Init 与开窗两条通道并发重入
        _dpcStarting = true;
        Task.Run(() =>
        {
            try
            {
                bool ok = _dpc.Start(observe ? 1000 : Cfg.DpcInterval, !observe && Cfg.DpcStreamOff == 1);
                if (ok)
                {
                    Thread.Sleep(3000);   // 启动暖机：开局 JIT/解密抖动会留下假尖峰
                    _dpc.ResetStats();
                }
                if (win == null)
                {
                    // 关窗竞态/托盘态：未定性（手动/自动都没启用）=不留驱动（零 DPC 流）；定性过=保留常驻
                    if (!_dpcKeepAlive && !_autoDriver) _dpc.Stop();
                    return;
                }
                Ui(() =>
                {
                    lblDpcState.Text = DpcStateText();
                    if (ok) StartDpcTimer();
                });
            }
            finally { _dpcStarting = false; }
        });
    }

    void StartDpcTimer()
    {
        if (_dpcTimer != null || win == null) return;
        _dpcTimer = new System.Windows.Threading.DispatcherTimer { Interval = TimeSpan.FromMilliseconds(300) };
        _dpcTimer.Tick += PollDpc;
        _dpcTimer.Start();
    }

    void PollDpc(object s, EventArgs e)
    {
        uint interval, min, max, avg;
        if (!_dpc.GetStats(out interval, out min, out max, out avg))
        {
            _dpcFail++;
            if (_dpcFail >= 5 && !_dpcReconnecting)
            {
                _dpcReconnecting = true;
                if (lblDpcState != null) lblDpcState.Text = "重连中…";
                Task.Run(() =>
                {
                    Thread.Sleep(800);
                    bool ok = _dpc.Start(1000, false);   // 重连只发生在开窗轮询中=观测模式，1ms
                    Ui(() =>
                    {
                        lblDpcState.Text = DpcStateText();
                        if (ok) _dpcFail = 0;
                        _dpcReconnecting = false;
                    });
                });
            }
            return;
        }
        _dpcFail = 0;
        // 驱动样本 = 周期 + 纯延迟，显示时减去周期（与 DPC Latency Checker 一致）
        long cur = (long)avg - interval; if (cur < 0) cur = 0;
        long hi = (long)max - interval; if (hi < 0) hi = 0;
        long lo = (long)min - interval; if (lo < 0) lo = 0;
        lblDpcAvg.Text = cur + " µs";
        lblDpcMax.Text = hi + " µs";
        lblDpcMin.Text = lo + " µs";
        _graph.Push(cur);
    }

    // ================= 测试流程 =================
    void SetTimerMode(bool manual)
    {
        if (_tuner.Running) return;
        timerManualMode = manual;
        timerAutoPanel.Visibility = manual ? Visibility.Collapsed : Visibility.Visible;
        timerManualPanel.Visibility = manual ? Visibility.Visible : Visibility.Collapsed;
        btnTimerMode.Content = manual ? "自动测试" : "手动输入";
        btnTimerMode.ToolTip = manual ? "返回自动测试模式" : "切换到手动输入设定值";
        if (manual)
        {
            uint v = _engine.Holding ? _engine.AppliedValue : (Cfg.TimerValue != 0 ? Cfg.TimerValue : Engine.StartValue);
            tbTimerManual.Text = v.ToString();
            tbTimerManual.Focus();
            tbTimerManual.SelectAll();
        }
    }

    void ApplyManualTimer()
    {
        uint v;
        if (!uint.TryParse(tbTimerManual.Text.Trim(), out v) || v == 0)
        {
            banner.Visibility = Visibility.Collapsed;
            lblStatus.Text = "手动设定：请输入十进制正整数（100ns 单位）";
            tbTimerManual.Focus(); tbTimerManual.SelectAll();
            return;
        }
        uint coarse, fine, cur;
        Native.NtQueryTimerResolution(out coarse, out fine, out cur);
        uint min = coarse < fine ? coarse : fine, max = coarse > fine ? coarse : fine;
        if (min == 0 || v < min || v > max)
        {
            banner.Visibility = Visibility.Collapsed;
            lblStatus.Text = min == 0 ? "手动设定：无法读取系统支持范围" : string.Format("手动设定：本机支持 {0}–{1}（100ns 单位）", min, max);
            tbTimerManual.Focus(); tbTimerManual.SelectAll();
            return;
        }

        _engine.Apply(v);
        uint res = _engine.CurrentResolution();
        Cfg.SaveKey("value", v.ToString());
        Cfg.SaveKey("resolution", res.ToString());
        Cfg.TimerValue = v; Cfg.TimerRes = res;
        tbTimerManual.Text = v.ToString();
        lblVal.Text = v.ToString();
        lblRes.Text = string.Format("{0:F4}ms", res / 10000.0);
        lblStatus.Text = "已应用手动设定";
        banner.Visibility = Visibility.Visible;
        bannerText.Text = string.Format("✓ 手动设定完成，已设定为 {0:F4}ms（设定值 {1}，已保存为预设）", res / 10000.0, v);
    }

    void StartTest()
    {
        banner.Visibility = Visibility.Collapsed;
        SetRunningUI(true);
        MonPause();   // 测试期间由测试流程驱动 slept 显示，DPC 轮询保持开启
        _gameLoad.Start();  // 模拟游戏环境的忽高忽低负载
        _tuner.RunAsync();
    }

    void SetRunningUI(bool running)
    {
        btnStart.IsEnabled = !running;
        btnStop.IsEnabled = running;
        btnTimerMode.IsEnabled = !running;
    }

    void OnFinished(bool ok, uint value, uint res)
    {
        _gameLoad.Stop();
        FlushDebugLog();
        if (ok)
        {
            Cfg.SaveKey("value", value.ToString());
            Cfg.SaveKey("resolution", res.ToString());
            Cfg.TimerValue = value; Cfg.TimerRes = res;
        }
        Ui(() =>
        {
            SetRunningUI(false);
            ResumeIdleLoops();
            banner.Visibility = Visibility.Visible;
            bannerText.Text = ok
                ? string.Format("✓ 设定完成，已设定为 {0:F4}ms（设定值 {1}，已保存为预设）", res / 10000.0, value)
                : string.Format("✗ 已达上限 {0} 仍未通过测试，保持当前设定值 {1}", Engine.MaxValue, value);
        });
    }

    void ResumeIdleLoops()
    {
        MonResume();   // 只经 Ui 包裹调用（窗口存活）
        if (_dpcTimer != null && _dpc.Ok) _dpcTimer.Start();
    }

    void UpdateStats(uint value, uint res, double slept)
    {
        Ui(() =>
        {
            if (value > 0) lblVal.Text = value.ToString();
            if (res > 0) lblRes.Text = string.Format("{0:F4}ms", res / 10000.0);
            if (slept > 0) SetSleptText(slept);
        });
    }

    void SetSleptText(double slept)
    {
        if (lblSlept == null) return;
        lblSlept.Text = string.Format("{0:F4}ms", slept);
        lblSlept.Foreground = Brush(slept <= Engine.Threshold ? "#111111" : "#111111");
    }

    void UpdateProgress(int cur, int max)
    {
        Ui(() => { pb.Maximum = max; pb.Value = cur; });
    }

    void UpdateStatus(string s)
    {
        Ui(() => lblStatus.Text = s);
    }

    static readonly List<string> _dbg = new List<string>();
    static void DebugLog(string s) { lock (_dbg) _dbg.Add(s); }
    static void FlushDebugLog()
    {
        try
        {
            lock (_dbg) { File.WriteAllLines(Path.Combine(Path.GetTempPath(), "dunsuitelite_run.log"), _dbg); _dbg.Clear(); }
        }
        catch { }
    }

    // ================= 自启 =================
    const string RunKey = @"Software\Microsoft\Windows\CurrentVersion\Run";
    // 老自启项迁移：值里没有 --tray 就补上（幂等，启动时跑一次）
    static void MigrateAutostartArg()
    {
        try
        {
            using (var k = Microsoft.Win32.Registry.CurrentUser.OpenSubKey(RunKey, true))
            {
                string v = k != null ? k.GetValue("DunSuiteLite") as string : null;
                if (!string.IsNullOrEmpty(v) && v.IndexOf("--tray", StringComparison.OrdinalIgnoreCase) < 0)
                    k.SetValue("DunSuiteLite", v.TrimEnd() + " --tray");
            }
        }
        catch { }
    }
    bool IsAutostart()
    {
        try
        {
            using (var k = Microsoft.Win32.Registry.CurrentUser.OpenSubKey(RunKey))
                return k != null && k.GetValue("DunSuiteLite") != null;
        }
        catch { return false; }
    }
    void SetAutostart(bool on)
    {
        try
        {
            using (var k = Microsoft.Win32.Registry.CurrentUser.OpenSubKey(RunKey, true))
            {
                if (on)
                {
                    k.SetValue("DunSuiteLite", "\"" + Assembly.GetExecutingAssembly().Location + "\" --tray");
                }
                else k.DeleteValue("DunSuiteLite", false);
            }
        }
        catch { }
        RefreshAutoVisual();
    }
    void RefreshAutoVisual()
    {
        if (autoCheck == null) return;
        autoCheck.Stroke = Brush(IsAutostart() ? "#111111" : "#D0D0D0");   // 勾=亮白 / 未勾=隐入背景
    }

    /* ---------------- 视觉工具 ---------------- */
    static SolidColorBrush Brush(string hex)
    {
        var b = new SolidColorBrush((Color)ColorConverter.ConvertFromString(hex));
        b.Freeze();
        return b;
    }

    static void StylePill(Border b, bool on)
    {
        b.Background = Brush(on ? "#111111" : "#E3E3E3");
        ((TextBlock)b.Child).Foreground = Brush(on ? "#FFFFFF" : "#666666");
    }

    // pill 微亮 hover（仅未选中态；选中态不动，hover 也不喧宾夺主）
    void HookPillHover(Border b, string mode)
    {
        b.MouseEnter += (s, e) => { if (memMode != mode) b.Background = Brush("#F3F3F3"); };
        b.MouseLeave += (s, e) => { if (memMode != mode) b.Background = Brush("#E3E3E3"); };
    }

    static void SetToggle(Border bg, System.Windows.Shapes.Ellipse knob, bool on)
    {
        bg.Background = Brush(on ? "#111111" : "#E3E3E3");
        knob.Fill = Brush(on ? "#FFFFFF" : "#666666");
        knob.HorizontalAlignment = on ? HorizontalAlignment.Right : HorizontalAlignment.Left;
    }

    /* ---------------- 右下角托盘菜单（自绘暗色面板；纯 Win32 + GDI+，不加载 WPF） ----------------
     * 10-18：换掉系统 TrackPopupMenu（灰白经典样式，无开关态）。自绘联动窗口满屏在跑，托盘期内存不变。
     * 结构：标题 / 打开主界面 / 快速开关（即时回放·录屏·滤镜）/ 立即清理待机 / 退出。
     * 交互：SetCapture 吃下所有点击，点窗外面=收起；开关行点完不关（方便连开两个）。 */
    const string TrayMenuCls = "DunSuiteLiteMenuCls";
    const int MR_OPEN = 1, MR_PURGE = 2, MR_EXIT = 3;
    const int MRT_HEADER = 10, MRT_SEP = 11, MRT_SECTION = 12;

    class TrayMenuRow
    {
        public int Kind;
        public string Label;
        public int Y, H;
        public bool Clickable { get { return Kind >= MR_OPEN && Kind <= MR_EXIT; } }
    }

    IntPtr _menuHwnd;
    TrayMenuWndProcDelegate _menuProc;
    bool _menuClassReg, _menuClosing;
    System.Drawing.Bitmap _menuBmp;
    int _menuW, _menuH, _menuX, _menuY, _menuHover = -1, _menuPressed = -1, _menuScale = 100;
    List<TrayMenuRow> _menuRows = new List<TrayMenuRow>();

    delegate IntPtr TrayMenuWndProcDelegate(IntPtr h, uint msg, IntPtr w, IntPtr l);

    // 菜单开着时挂 WH_MOUSE_LL：点菜单外的任何地方都收起（捕获在 NOACTIVATE 窗口上不可靠，实测点了不关）
    const int WH_MOUSE_LL = 14;
    const int WM_LBTNDOWN = 0x0201, WM_RBTNDOWN = 0x0204, WM_MBTNDOWN = 0x0207;
    delegate IntPtr LowLevelMouseProc(int nCode, IntPtr wParam, IntPtr lParam);
    static readonly LowLevelMouseProc _menuMouseProc = TrayMenuMouseHook;   // 反向 P/Invoke 委托必须一次创建常驻
    static SuiteApp _menuApp;
    IntPtr _menuMouseHook;
    [StructLayout(LayoutKind.Sequential)] struct MSLLHOOKSTRUCT { public POINT pt; public uint mouseData, flags, time; public IntPtr dwExtraInfo; }

    static IntPtr TrayMenuMouseHook(int nCode, IntPtr wParam, IntPtr lParam)
    {
        try
        {
            var app = _menuApp;
            if (nCode >= 0 && app != null && app._menuHwnd != IntPtr.Zero)
            {
                int m = wParam.ToInt32();
                if (m == WM_LBTNDOWN || m == WM_RBTNDOWN || m == WM_MBTNDOWN)
                {
                    var info = (MSLLHOOKSTRUCT)Marshal.PtrToStructure(lParam, typeof(MSLLHOOKSTRUCT));
                    bool inside = info.pt.X >= app._menuX && info.pt.X < app._menuX + app._menuW
                               && info.pt.Y >= app._menuY && info.pt.Y < app._menuY + app._menuH;
                    if (!inside) PostMessage(app._menuHwnd, 0x0010, IntPtr.Zero, IntPtr.Zero);   // WM_CLOSE → 主线程收起
                }
            }
            return CallNextHookEx(IntPtr.Zero, nCode, wParam, lParam);
        }
        catch { return CallNextHookEx(IntPtr.Zero, nCode, wParam, lParam); }
    }

    [DllImport("user32.dll")] static extern bool UpdateLayeredWindow(IntPtr hwnd, IntPtr hdcDst, ref POINT pptDst, ref SIZEW psize, IntPtr hdcSrc, ref POINT pptSrc, uint crKey, ref BLENDFUNCTION pblend, uint dwFlags);
    [DllImport("user32.dll")] static extern IntPtr GetDC(IntPtr hWnd);
    [DllImport("user32.dll")] static extern int ReleaseDC(IntPtr hWnd, IntPtr hDC);
    [DllImport("user32.dll", SetLastError = true)] static extern IntPtr SetWindowsHookExW(int idHook, LowLevelMouseProc lpfn, IntPtr hMod, uint dwThreadId);
    [DllImport("user32.dll")] static extern bool UnhookWindowsHookEx(IntPtr hhk);
    [DllImport("user32.dll")] static extern IntPtr CallNextHookEx(IntPtr hhk, int nCode, IntPtr wParam, IntPtr lParam);
    [DllImport("kernel32.dll", CharSet = CharSet.Unicode)] static extern IntPtr GetModuleHandleW(string name);
    [DllImport("user32.dll")] static extern bool ShowWindow(IntPtr hWnd, int nCmdShow);
    [DllImport("user32.dll")] static extern bool DestroyWindow(IntPtr hWnd);
    [DllImport("gdi32.dll")] static extern IntPtr CreateCompatibleDC(IntPtr hdc);
    [DllImport("gdi32.dll")] static extern bool DeleteDC(IntPtr hdc);
    [DllImport("gdi32.dll")] static extern IntPtr SelectObject(IntPtr hdc, IntPtr h);
    [DllImport("gdi32.dll")] static extern bool DeleteObject(IntPtr ho);
    [DllImport("user32.dll")] static extern bool TrackMouseEvent(ref TRACKMOUSEEVENT tme);
    [DllImport("user32.dll", CharSet = CharSet.Unicode)] static extern bool SystemParametersInfoW(uint action, uint param, out RECT rect, uint winIni);

    [StructLayout(LayoutKind.Sequential)] struct SIZEW { public int cx, cy; }
    [StructLayout(LayoutKind.Sequential)] struct RECT { public int Left, Top, Right, Bottom; }
    [StructLayout(LayoutKind.Sequential)] struct TRACKMOUSEEVENT { public int cbSize; public uint dwFlags; public IntPtr hwndTrack; public uint dwHoverTime; }
    [StructLayout(LayoutKind.Sequential)] struct BLENDFUNCTION { public byte BlendOp, BlendFlags, SourceConstantAlpha, AlphaFormat; }

    void ShowTrayMenu()
    {
        if (_menuHwnd != IntPtr.Zero) { CloseTrayMenu(); return; }   // 再点托盘=收起

        float s = 1f;
        try { using (var g = System.Drawing.Graphics.FromHwnd(IntPtr.Zero)) s = Math.Max(1f, g.DpiX / 96f); } catch { }
        _menuScale = (int)Math.Round(s * 100);

        var rows = new List<TrayMenuRow>();
        int y = 0;
        Action<int, string, int> add = delegate(int kind, string label, int h)
        {
            rows.Add(new TrayMenuRow { Kind = kind, Label = label, Y = y, H = h });
            y += h;
        };
        int item = (int)(31 * s), sep = (int)(7 * s), section = (int)(17 * s), header = (int)(38 * s);
        add(MRT_HEADER, null, header);
        add(MRT_SEP, null, sep);
        add(MR_OPEN, "打开主界面", item);
        add(MRT_SEP, null, sep);
        add(MRT_SEP, null, sep);
        add(MR_PURGE, "立即清理待机", item);
        add(MRT_SEP, null, sep);
        add(MR_EXIT, "退出", item);
        _menuRows = rows;
        _menuW = (int)(214 * s);
        _menuH = y;

        POINT pt; GetCursorPos(out pt);
        int gap = (int)(10 * s);
        _menuX = pt.X - _menuW + gap;
        _menuY = pt.Y - _menuH - gap;
        RECT wa;
        if (SystemParametersInfoW(0x0030, 0, out wa, 0))
        {
            if (_menuY < wa.Top + 8) _menuY = pt.Y + gap;
            if (_menuX + _menuW > wa.Right - 8) _menuX = wa.Right - 8 - _menuW;
            if (_menuX < wa.Left + 8) _menuX = wa.Left + 8;
            if (_menuY + _menuH > wa.Bottom - 8) _menuY = wa.Bottom - 8 - _menuH;
        }

        if (!_menuClassReg)
        {
            _menuProc = TrayMenuProc;
            var wc = new WNDCLASSEX
            {
                cbSize = (uint)Marshal.SizeOf(typeof(WNDCLASSEX)),
                lpfnWndProc = Marshal.GetFunctionPointerForDelegate(_menuProc),
                lpszClassName = TrayMenuCls
            };
            RegisterClassEx(ref wc);
            _menuClassReg = true;
        }
        // WS_POPUP | WS_EX_TOOLWINDOW|TOPMOST|NOACTIVATE|LAYERED
        _menuHwnd = CreateWindowExW(0x8 | 0x08000000 | 0x80 | 0x80000, TrayMenuCls, "DunSuiteLiteMenu", 0x80000000,
            _menuX, _menuY, _menuW, _menuH, IntPtr.Zero, IntPtr.Zero, IntPtr.Zero, IntPtr.Zero);
        if (_menuHwnd == IntPtr.Zero) return;

        _menuHover = -1;
        _menuPressed = -1;
        _menuApp = this;
        DrawTrayMenu();
        ShowWindow(_menuHwnd, 8);   // SW_SHOWNA：不抢焦点
        // 低层鼠标钩子兜底：点菜单外任意位置收起（SetCapture 在 NOACTIVATE 窗口上实测无效）
        if (_menuMouseHook == IntPtr.Zero)
            _menuMouseHook = SetWindowsHookExW(WH_MOUSE_LL, _menuMouseProc, GetModuleHandleW(null), 0);
    }

    void CloseTrayMenu()
    {
        if (_menuMouseHook != IntPtr.Zero)
        {
            try { UnhookWindowsHookEx(_menuMouseHook); } catch { }
            _menuMouseHook = IntPtr.Zero;
        }
        _menuApp = null;
        if (_menuHwnd == IntPtr.Zero) { _menuRows = new List<TrayMenuRow>(); return; }
        _menuClosing = true;
        try { DestroyWindow(_menuHwnd); }
        catch { }
        finally
        {
            _menuHwnd = IntPtr.Zero;
            _menuClosing = false;
        }
        if (_menuBmp != null) { try { _menuBmp.Dispose(); } catch { } _menuBmp = null; }
        _menuRows = new List<TrayMenuRow>();
        _menuHover = -1; _menuPressed = -1;
    }

    IntPtr TrayMenuProc(IntPtr h, uint msg, IntPtr w, IntPtr l)
    {
        const uint WM_MOUSEMOVE = 0x0200, WM_LBUTTONDOWN = 0x0201, WM_LBUTTONUP = 0x0202;
        if (msg == WM_MOUSEMOVE)
        {
            int hover = TrayMenuHit(l);
            if (hover != _menuHover) { _menuHover = hover; DrawTrayMenu(); }
            var tme = new TRACKMOUSEEVENT { cbSize = Marshal.SizeOf(typeof(TRACKMOUSEEVENT)), dwFlags = 2, hwndTrack = h };   // TME_LEAVE
            TrackMouseEvent(ref tme);
            return IntPtr.Zero;
        }
        if (msg == WM_LBUTTONDOWN)
        {
            int row = TrayMenuHit(l);
            if (row < 0) { CloseTrayMenu(); return IntPtr.Zero; }
            _menuPressed = row;
            DrawTrayMenu();
            return IntPtr.Zero;
        }
        if (msg == WM_LBUTTONUP)
        {
            int row = TrayMenuHit(l);
            int pressed = _menuPressed;
            _menuPressed = -1;
            if (row < 0) { CloseTrayMenu(); return IntPtr.Zero; }
            if (row == pressed && row < _menuRows.Count && _menuRows[row].Clickable)
            {
                int kind = _menuRows[row].Kind;
                CloseTrayMenu();
                TrayMenuActivate(kind);
            }
            else DrawTrayMenu();
            return IntPtr.Zero;
        }
        if (msg == 0x02A3)   // WM_MOUSELEAVE
        {
            if (_menuHover != -1) { _menuHover = -1; DrawTrayMenu(); }
            return IntPtr.Zero;
        }
        if (msg == 0x0010)   // WM_CLOSE（低层鼠标钩子检测到点外面）→ 收起
        {
            CloseTrayMenu();
            return IntPtr.Zero;
        }
        if (msg == 0x0215)   // WM_CAPTURECHANGED：点到别处（或自己销毁）→ 收起
        {
            if (!_menuClosing) CloseTrayMenu();
            return IntPtr.Zero;
        }
        if (msg == 0x0021) return (IntPtr)3;   // WM_MOUSEACTIVATE → MA_NOACTIVATE
        if (msg == 0x000F) return IntPtr.Zero;  // WM_PAINT：整窗自绘
        if (msg == 0x0002) { _menuHwnd = IntPtr.Zero; return IntPtr.Zero; }   // WM_DESTROY
        return DefWindowProcW(h, msg, w, l);
    }

    int TrayMenuHit(IntPtr l)
    {
        int lp = l.ToInt32();
        int x = (short)(lp & 0xFFFF), y = (short)((lp >> 16) & 0xFFFF);
        for (int i = 0; i < _menuRows.Count; i++)
        {
            var r = _menuRows[i];
            if (!r.Clickable) continue;
            if (y >= r.Y && y < r.Y + r.H) return i;
        }
        return -1;
    }

    void TrayMenuActivate(int kind)
    {
        switch (kind)
        {
            case MR_OPEN:
                ShowMain();
                EnsureTrayAlive();
                break;
            case MR_PURGE:
                new Thread(() => DoPurge("手动", false)) { IsBackground = true }.Start();
                break;
            case MR_EXIT:
                ExitApp();
                break;
        }
    }

    static System.Drawing.Drawing2D.GraphicsPath TrayRoundRect(float x, float y, float w, float h, float r)
    {
        var p = new System.Drawing.Drawing2D.GraphicsPath();
        float d = r * 2;
        p.AddArc(x, y, d, d, 180, 90);
        p.AddArc(x + w - d, y, d, d, 270, 90);
        p.AddArc(x + w - d, y + h - d, d, d, 0, 90);
        p.AddArc(x, y + h - d, d, d, 90, 90);
        p.CloseFigure();
        return p;
    }

    void DrawTrayMenu()
    {
        if (_menuHwnd == IntPtr.Zero || _menuRows.Count == 0) return;
        try
        {
            if (_menuBmp != null) { _menuBmp.Dispose(); _menuBmp = null; }
            _menuBmp = new System.Drawing.Bitmap(_menuW, _menuH, System.Drawing.Imaging.PixelFormat.Format32bppPArgb);
            float s = _menuScale / 100f;
            using (var g = System.Drawing.Graphics.FromImage(_menuBmp))
            {
                g.SmoothingMode = System.Drawing.Drawing2D.SmoothingMode.AntiAlias;
                g.TextRenderingHint = System.Drawing.Text.TextRenderingHint.AntiAlias;
                g.PixelOffsetMode = System.Drawing.Drawing2D.PixelOffsetMode.HighQuality;
                var full = new System.Drawing.RectangleF(0, 0, _menuW - 0.5f, _menuH - 0.5f);
                using (var path = TrayRoundRect(0.5f, 0.5f, _menuW - 1f, _menuH - 1f, 10f * s))
                {
                    using (var bg = new System.Drawing.Drawing2D.LinearGradientBrush(full,
                        System.Drawing.Color.FromArgb(0xFF, 0xFF, 0xFF, 0xFF), System.Drawing.Color.FromArgb(0xFF, 0xF3, 0xF3, 0xF3), 90f))
                        g.FillPath(bg, path);
                    using (var bd = new System.Drawing.Pen(System.Drawing.Color.FromArgb(0xFF, 0xE3, 0xE3, 0xE3), 1f))
                        g.DrawPath(bd, path);
                }
                using (var fTitle = new System.Drawing.Font("Microsoft YaHei UI", 11.5f * s, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Pixel))
                using (var fSub = new System.Drawing.Font("Microsoft YaHei UI", 8f * s, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Pixel))
                using (var fItem = new System.Drawing.Font("Microsoft YaHei UI", 10.5f * s, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Pixel))
                using (var fTitleBr = new System.Drawing.SolidBrush(System.Drawing.Color.FromArgb(0xFF, 0x11, 0x11, 0x11)))
                using (var fSubBr = new System.Drawing.SolidBrush(System.Drawing.Color.FromArgb(0xFF, 0x88, 0x88, 0x88)))
                using (var fItemBr = new System.Drawing.SolidBrush(System.Drawing.Color.FromArgb(0xFF, 0x33, 0x33, 0x33)))
                using (var fItemHotBr = new System.Drawing.SolidBrush(System.Drawing.Color.FromArgb(0xFF, 0x11, 0x11, 0x11)))
                using (var sf = new System.Drawing.StringFormat { LineAlignment = System.Drawing.StringAlignment.Center, Alignment = System.Drawing.StringAlignment.Near, FormatFlags = System.Drawing.StringFormatFlags.NoWrap })
                {
                    for (int i = 0; i < _menuRows.Count; i++)
                    {
                        var r = _menuRows[i];
                        bool hover = i == _menuHover && r.Clickable;
                        bool press = hover && i == _menuPressed;
                        if (r.Kind == MRT_HEADER)
                        {
                            g.DrawString("DunSuite Lite", fTitle, fTitleBr, 14f * s, 8f * s);
                            g.DrawString("性能套件 · 托盘常驻", fSub, fSubBr, 14f * s, 23f * s);
                            using (var dot = new System.Drawing.SolidBrush(System.Drawing.Color.FromArgb(0xFF, 0x11, 0x11, 0x11)))
                                g.FillEllipse(dot, _menuW - 20f * s, 17f * s, 4.5f * s, 4.5f * s);
                        }
                        else if (r.Kind == MRT_SEP)
                        {
                            using (var ln = new System.Drawing.Pen(System.Drawing.Color.FromArgb(0xFF, 0xE3, 0xE3, 0xE3), 1f))
                                g.DrawLine(ln, 12f * s, r.Y + r.H / 2f, _menuW - 12f * s, r.Y + r.H / 2f);
                        }
                        else
                        {
                            if (hover)
                            {
                                using (var hl = TrayRoundRect(6f * s, r.Y + 1.5f * s, _menuW - 12f * s, r.H - 3f * s, 7f * s))
                                using (var br = new System.Drawing.SolidBrush(System.Drawing.Color.FromArgb(press ? 0xFF : 0xD0, 0xE3, 0xE3, 0xE3)))
                                    g.FillPath(br, hl);
                            }
                            var iconColor = System.Drawing.Color.FromArgb(0xFF, hover ? 0x0F : 0x64, hover ? 0x17 : 0x74, hover ? 0x2A : 0x8B);
                            DrawTrayIcon(g, r.Kind, 20f * s, r.Y + r.H / 2f, s, iconColor);
                            g.DrawString(r.Label, fItem, hover ? fItemHotBr : fItemBr,
                                new System.Drawing.RectangleF(35f * s, r.Y, _menuW - 49f * s, r.H), sf);
                        }
                    }
                }
            }
            PushTrayMenuBitmap();
        }
        catch { }
    }



    static void DrawTrayIcon(System.Drawing.Graphics g, int kind, float cx, float cy, float s, System.Drawing.Color c)
    {
        float r = 5.5f * s;
        using (var pen = new System.Drawing.Pen(c, 1.3f * s))
        {
            pen.StartCap = System.Drawing.Drawing2D.LineCap.Round;
            pen.EndCap = System.Drawing.Drawing2D.LineCap.Round;
            if (kind == MR_OPEN)
            {
                g.DrawRectangle(pen, cx - r, cy - r, 2 * r, 2 * r);
                g.DrawLine(pen, cx, cy - r, cx, cy + r);
                g.DrawLine(pen, cx - r, cy, cx + r, cy);
            }
            else if (kind == MR_PURGE)
            {
                var star = new[]
                {
                    new System.Drawing.PointF(cx, cy - r - 1f * s), new System.Drawing.PointF(cx + 1.5f * s, cy - 1.5f * s),
                    new System.Drawing.PointF(cx + r + 1f * s, cy), new System.Drawing.PointF(cx + 1.5f * s, cy + 1.5f * s),
                    new System.Drawing.PointF(cx, cy + r + 1f * s), new System.Drawing.PointF(cx - 1.5f * s, cy + 1.5f * s),
                    new System.Drawing.PointF(cx - r - 1f * s, cy), new System.Drawing.PointF(cx - 1.5f * s, cy - 1.5f * s)
                };
                using (var br = new System.Drawing.SolidBrush(c)) g.FillPolygon(br, star);
            }
            else if (kind == MR_EXIT)
            {
                g.DrawArc(pen, cx - r, cy - r, 2 * r, 2 * r, -55, 290);
                g.DrawLine(pen, cx, cy - r - 1f * s, cx, cy - 1f * s);
            }
        }
    }

    void PushTrayMenuBitmap()
    {
        if (_menuHwnd == IntPtr.Zero || _menuBmp == null) return;
        IntPtr screenDc = GetDC(IntPtr.Zero);
        if (screenDc == IntPtr.Zero) return;
        IntPtr memDc = CreateCompatibleDC(screenDc);
        IntPtr hBmp = _menuBmp.GetHbitmap(System.Drawing.Color.FromArgb(0));
        IntPtr old = SelectObject(memDc, hBmp);
        var size = new SIZEW { cx = _menuW, cy = _menuH };
        var src = new POINT { X = 0, Y = 0 };
        var dst = new POINT { X = _menuX, Y = _menuY };
        var blend = new BLENDFUNCTION { BlendOp = 0, BlendFlags = 0, SourceConstantAlpha = 255, AlphaFormat = 1 };
        UpdateLayeredWindow(_menuHwnd, screenDc, ref dst, ref size, memDc, ref src, 0, ref blend, 2);   // ULW_ALPHA
        SelectObject(memDc, old);
        DeleteObject(hBmp);
        DeleteDC(memDc);
        ReleaseDC(IntPtr.Zero, screenDc);
    }
}

// ================= 原生 API（计时器/DPC/守护用） =================
static class Native
{
    [DllImport("ntdll.dll")] public static extern uint NtSetTimerResolution(uint req, bool set, out uint cur);
    [DllImport("ntdll.dll")] public static extern uint NtQueryTimerResolution(out uint min, out uint max, out uint cur);
    [DllImport("kernel32.dll")] public static extern bool QueryPerformanceCounter(out long v);
    [DllImport("kernel32.dll")] public static extern long GetTickCount64();   // 更新频率=全局时钟中断（KUSER_SHARED_DATA），与自身计时器请求无关
    [DllImport("kernel32.dll")] public static extern bool QueryPerformanceFrequency(out long v);
    [DllImport("kernel32.dll")] public static extern IntPtr GetCurrentThread();
    [DllImport("kernel32.dll")] public static extern IntPtr SetThreadAffinityMask(IntPtr h, IntPtr mask);
    [DllImport("kernel32.dll")] public static extern IntPtr GetCurrentProcess();
    [DllImport("kernel32.dll")] public static extern bool SetPriorityClass(IntPtr h, uint p);
    // 电源节流：防止系统把本进程的计时器请求标记为"挂起不计"（LOL 对局后实测被降级）
    [DllImport("kernel32.dll", SetLastError = true)] public static extern bool SetProcessInformation(IntPtr h, int cls, IntPtr info, int size);
    [StructLayout(LayoutKind.Sequential)]
    public struct PROCESS_POWER_THROTTLING_STATE { public uint Version; public uint ControlMask; public uint StateMask; }
    [DllImport("psapi.dll")] public static extern bool EmptyWorkingSet(IntPtr hProcess);
    public const uint BelowNormalPriorityClass = 0x4000;

    // 待机内存清理通道
    [DllImport("ntdll.dll")] public static extern int NtSetSystemInformation(int cls, ref int cmd, int len);
    [DllImport("ntdll.dll")] public static extern int NtQuerySystemInformation(int cls, IntPtr buf, int len, out int retLen);
    [DllImport("psapi.dll")] public static extern bool GetPerformanceInfo(out PERF_INFO pi, int size);
    [DllImport("kernel32.dll")] public static extern IntPtr CreateMemoryResourceNotification(int type);
    [StructLayout(LayoutKind.Sequential)]
    public struct PERF_INFO { public int cb; public IntPtr CommitTotal, CommitLimit, CommitPeak, PhysicalTotal, PhysicalAvailable, SystemCache, KernelTotal, KernelPaged, KernelNonpaged, PageSize; public int HandleCount, ProcessCount, ThreadCount; }

    [DllImport("kernel32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    public static extern IntPtr CreateFile(string name, uint access, uint share, IntPtr sec, uint disp, uint flags, IntPtr tmpl);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool DeviceIoControl(IntPtr h, uint code, byte[] inBuf, uint inLen, byte[] outBuf, uint outLen, out uint ret, IntPtr ovl);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool CloseHandle(IntPtr h);

    [DllImport("kernel32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    public static extern IntPtr CreateFileMapping(IntPtr hFile, IntPtr sec, uint protect, uint maxHi, uint maxLo, string name);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr MapViewOfFile(IntPtr map, uint access, uint offHi, uint offLo, uint size);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool UnmapViewOfFile(IntPtr view);
    [DllImport("kernel32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    public static extern IntPtr LoadLibrary(string path);
    [DllImport("kernel32.dll", SetLastError = true, CharSet = CharSet.Ansi)]
    public static extern IntPtr GetProcAddress(IntPtr mod, string name);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool FreeLibrary(IntPtr mod);
    [DllImport("user32.dll", SetLastError = true)]
    public static extern IntPtr SetWindowsHookEx(int idHook, IntPtr proc, IntPtr mod, uint threadId);
    [DllImport("user32.dll", SetLastError = true)]
    public static extern bool UnhookWindowsHookEx(IntPtr hook);

    // 显示器物理分辨率（录屏页显示器下拉用；Screen.AllScreens 在 DPI 缩放下拿的是逻辑分辨率）
    [DllImport("user32.dll", CharSet = CharSet.Unicode)]
    public static extern bool EnumDisplayDevices(string lpDevice, uint i, ref DISPLAY_DEVICE lpDisplayDevice, uint dwFlags);
    [DllImport("user32.dll", CharSet = CharSet.Unicode)]
    public static extern bool EnumDisplaySettings(string lpszDeviceName, int iModeNum, ref DEVMODE lpDevMode);   // iModeNum=-1=ENUM_CURRENT_SETTINGS
    [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Unicode)]
    public struct DISPLAY_DEVICE
    {
        public int cb;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 32)] public string DeviceName;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 128)] public string DeviceString;
        public int StateFlags;   // 1=ATTACHED_TO_DESKTOP 4=PRIMARYDEVICE
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 128)] public string DeviceID;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 128)] public string DeviceKey;
    }
    [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Unicode)]
    public struct DEVMODE
    {
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 32)] public string dmDeviceName;
        public ushort dmSpecVersion, dmDriverVersion, dmSize, dmDriverExtra;
        public uint dmFields;
        public int dmPositionX, dmPositionY;   // union 16B：POINTL(8) + DisplayOrientation(4) + DisplayFixedOutput(4)（另一形态=8 个 SHORT 打印字段）
        public uint dmDisplayOrientation, dmDisplayFixedOutput;
        public short dmColor, dmDuplex, dmYResolution, dmTTOption, dmCollate;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 32)] public string dmFormName;
        public ushort dmLogPixels;
        public uint dmBitsPerPel, dmPelsWidth, dmPelsHeight, dmDisplayFlags, dmDisplayFrequency;
        public uint dmICMMethod, dmICMIntent, dmMediaType, dmDitherType, dmReserved1, dmReserved2, dmPanningWidth, dmPanningHeight;
    }

    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr OpenProcess(uint access, bool inherit, int pid);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr VirtualAllocEx(IntPtr hProc, IntPtr addr, uint size, uint type, uint protect);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool VirtualFreeEx(IntPtr hProc, IntPtr addr, uint size, uint type);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool WriteProcessMemory(IntPtr hProc, IntPtr addr, byte[] buf, uint size, out uint written);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr CreateRemoteThread(IntPtr hProc, IntPtr sa, uint stack, IntPtr start, IntPtr param, uint flags, IntPtr tid);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern uint WaitForSingleObject(IntPtr h, uint ms);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool GetExitCodeThread(IntPtr h, out uint code);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool IsWow64Process(IntPtr hProc, out bool wow64);
    [DllImport("kernel32.dll", CharSet = CharSet.Unicode)]
    public static extern IntPtr GetModuleHandle(string name);
    [DllImport("advapi32.dll", SetLastError = true)]
    public static extern bool OpenProcessToken(IntPtr hProc, uint access, out IntPtr tok);
    [DllImport("advapi32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    public static extern bool LookupPrivilegeValue(string sys, string name, out long luid);
    [DllImport("advapi32.dll", SetLastError = true)]
    public static extern bool AdjustTokenPrivileges(IntPtr tok, bool disableAll, ref TOKEN_PRIVILEGES tp, uint len, IntPtr prev, IntPtr retLen);
    // LUID 拆两个 int：Windows LUID 是双 DWORD 结构体（4 字节对齐），C# long 按 8 对齐会把 Luid 错到 offset 8
    // → AdjustTokenPrivileges 读垃圾 LUID 报 1300 静默失败（2026-08-16 实测确诊）
    [StructLayout(LayoutKind.Sequential)]
    public struct TOKEN_PRIVILEGES { public int Count; public int LuidLow; public int LuidHigh; public int Attr; }

    [DllImport("advapi32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    public static extern IntPtr OpenSCManager(string machine, string db, uint access);
    [DllImport("advapi32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    public static extern IntPtr CreateService(IntPtr scm, string name, string display, uint access, uint type, uint start, uint errctl, string path, string loadorder, IntPtr tag, string deps, string user, string pass);
    [DllImport("advapi32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    public static extern IntPtr OpenService(IntPtr scm, string name, uint access);
    [DllImport("advapi32.dll", SetLastError = true)]
    public static extern bool StartService(IntPtr svc, uint argc, IntPtr argv);
    [DllImport("advapi32.dll", SetLastError = true)]
    public static extern bool ControlService(IntPtr svc, uint ctrl, out SERVICE_STATUS st);
    [DllImport("advapi32.dll", SetLastError = true)]
    public static extern bool DeleteService(IntPtr svc);
    [DllImport("advapi32.dll", SetLastError = true)]
    public static extern bool CloseServiceHandle(IntPtr h);

    [StructLayout(LayoutKind.Sequential)]
    public struct SERVICE_STATUS { public uint type, state, accept, exit, svcExit, hint, wait; }

    [DllImport("user32.dll", SetLastError = true)]
    public static extern bool RegisterShellHookWindow(IntPtr hWnd);
    [DllImport("user32.dll", SetLastError = true)]
    public static extern bool DeregisterShellHookWindow(IntPtr hWnd);
    [DllImport("user32.dll", CharSet = CharSet.Unicode)]
    public static extern uint RegisterWindowMessage(string s);
    [DllImport("user32.dll")]
    public static extern uint GetWindowThreadProcessId(IntPtr hWnd, out uint pid);
    [DllImport("user32.dll")]
    public static extern IntPtr GetForegroundWindow();
    [DllImport("user32.dll")]
    public static extern bool GetWindowRect(IntPtr hWnd, out RECT lpRect);   // 录屏「仅游戏时」全屏兜底判定用
    [DllImport("user32.dll")]
    public static extern int GetSystemMetrics(int nIndex);
    [StructLayout(LayoutKind.Sequential)]
    public struct RECT { public int Left, Top, Right, Bottom; }

    // 核心隔离：亲和性 + 拓扑
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool SetProcessAffinityMask(IntPtr h, UIntPtr mask);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool GetProcessAffinityMask(IntPtr h, out UIntPtr procMask, out UIntPtr sysMask);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool GetLogicalProcessorInformationEx(int type, IntPtr buffer, ref uint len);

    // 首核调度：线程句柄 + 线程时间（强身份） + Ideal + CPU Sets
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr OpenThread(uint access, bool inherit, uint tid);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool GetThreadTimes(IntPtr h, out long create, out long exit, out long kernel, out long user);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool GetProcessTimes(IntPtr h, out long create, out long exit, out long kernel, out long user);
    [StructLayout(LayoutKind.Sequential)]
    public struct PROCESSOR_NUMBER { public ushort Group; public byte Number; public byte Reserved; public ushort Reserved2; }
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool GetThreadIdealProcessorEx(IntPtr h, out PROCESSOR_NUMBER num);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool SetThreadIdealProcessorEx(IntPtr h, ref PROCESSOR_NUMBER num, out PROCESSOR_NUMBER prev);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool GetThreadSelectedCpuSets(IntPtr h, uint[] ids, uint count, out uint required);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool SetThreadSelectedCpuSets(IntPtr h, uint[] ids, uint count);
    // 软隔离：进程级 CPU Sets（默认集=软引导，可溢出；仅 Win10 1709+ 导出，ProcCpuSetsOk 探测防老系统 EntryPointNotFound）
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool SetProcessDefaultCpuSets(IntPtr h, IntPtr ids, uint count);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool GetProcessDefaultCpuSets(IntPtr h, IntPtr ids, uint len, out uint required);
    static bool? _procCpuSetsOk;
    public static bool ProcCpuSetsOk
    {
        get
        {
            if (_procCpuSetsOk == null)
            {
                try { _procCpuSetsOk = GetProcAddress(GetModuleHandle("kernel32.dll"), "SetProcessDefaultCpuSets") != IntPtr.Zero; }
                catch { _procCpuSetsOk = false; }
            }
            return _procCpuSetsOk.Value;
        }
    }
    // 算法 C 硬绑：GroupAffinity（经典硬掩码，与 CPU Sets 互斥——写 affinity 前必须先清 Sets）
    [StructLayout(LayoutKind.Sequential)]
    public struct GROUP_AFFINITY { public UIntPtr Mask; public ushort Group; public ushort R0; public ushort R1; public ushort R2; }
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool SetThreadGroupAffinity(IntPtr h, ref GROUP_AFFINITY affinity, out GROUP_AFFINITY prev);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool GetThreadGroupAffinity(IntPtr h, out GROUP_AFFINITY affinity);
    // GetSystemCpuSetInformation 只动态加载（老系统没有此导出，硬模式要优雅降级）
    [UnmanagedFunctionPointer(CallingConvention.Winapi)]
    public delegate bool GetSysCpuSetInfo(IntPtr info, uint bufLen, out uint retLen, IntPtr hProcess, uint flags);

    // 首核调度主线程识别：线程枚举 + 线程起始地址 + 主模块范围
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr CreateToolhelp32Snapshot(uint flags, uint pid);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool Thread32First(IntPtr snap, ref THREADENTRY32 te);
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool Thread32Next(IntPtr snap, ref THREADENTRY32 te);
    [StructLayout(LayoutKind.Sequential)]
    public struct THREADENTRY32 { public uint dwSize; public uint cntUsage; public uint th32ThreadID; public uint th32OwnerProcessID; public int tpBasePri; public int tpDeltaPri; public uint dwFlags; }
    [DllImport("ntdll.dll")]
    public static extern int NtQueryInformationThread(IntPtr h, int infoClass, out IntPtr data, int len, IntPtr retLen);
    [DllImport("psapi.dll", SetLastError = true)]
    public static extern bool EnumProcessModules(IntPtr hProc, [Out] IntPtr[] mods, uint bytes, out uint needed);
    [DllImport("psapi.dll", SetLastError = true)]
    public static extern bool GetModuleInformation(IntPtr hProc, IntPtr mod, out MODULEINFO info, uint size);
    [StructLayout(LayoutKind.Sequential)]
    public struct MODULEINFO { public IntPtr lpBaseOfDll; public uint SizeOfImage; public IntPtr EntryPoint; }

    public static readonly IntPtr InvalidHandle = new IntPtr(-1);
}

static class Cfg
{
    public static readonly string Dir = Path.Combine(Environment.GetEnvironmentVariable("ProgramData") ?? @"C:\ProgramData", "DunSuiteLite");
    static readonly string File = Path.Combine(Dir, "config.ini");
    public static uint TimerValue, TimerRes;
    public static uint DpcInterval = 1000;
    public static int DpcUnlock = 1;
    public static int DpcStreamOff = 0;
    public static string MemMode = "smart";
    public static int MemThreshold = 1024;
    public static int MemInterval = 30;
    public static bool MemHotkey = false;
    public static readonly Dictionary<string, int> SliceRules = new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase);
    public static ulong IsoMask;
    public static int IsoSoft;
    public static ulong SoftGameMask;
    public static ulong SoftIsoMask;
    public static string IrqMode;
    public static ulong IrqMask;
    public static readonly HashSet<string> IsoGames = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
    public static readonly HashSet<string> IsoBackgrounds = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
    public static readonly Dictionary<string, int> FcRules = new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase);

    public static int IsoRuleMode(string name)
    {
        lock (IsoGames) if (IsoGames.Contains(name)) return 1;
        lock (IsoBackgrounds) if (IsoBackgrounds.Contains(name)) return 2;
        return 0;
    }

    public static int IsoRuleCount()
    {
        lock (IsoGames) lock (IsoBackgrounds) return IsoGames.Count + IsoBackgrounds.Count;
    }

    public static void Load()
    {
        try
        {
            if (!System.IO.File.Exists(File)) return;
            foreach (var raw in System.IO.File.ReadAllLines(File))
            {
                var t = raw.Trim();
                int eq = t.IndexOf('=');
                if (eq <= 0) continue;
                string k = t.Substring(0, eq).Trim(), v = t.Substring(eq + 1).Trim();
                uint u;
                if (k.Equals("value", StringComparison.OrdinalIgnoreCase) && uint.TryParse(v, out u)) TimerValue = u;
                else if (k.Equals("resolution", StringComparison.OrdinalIgnoreCase) && uint.TryParse(v, out u)) TimerRes = u;
                else if (k.Equals("DpcInterval", StringComparison.OrdinalIgnoreCase) && uint.TryParse(v, out u) && u >= 1000) DpcInterval = u;
                else if (k.Equals("DpcUnlock", StringComparison.OrdinalIgnoreCase)) DpcUnlock = v == "1" ? 1 : 0;
                else if (k.Equals("DpcStreamOff", StringComparison.OrdinalIgnoreCase)) DpcStreamOff = v == "1" ? 1 : 0;
                else if (k.Equals("Mode", StringComparison.OrdinalIgnoreCase) && (v == "off" || v == "event" || v == "standby" || v == "timer" || v == "smart"))
                    MemMode = (v == "event" || v == "standby") ? "smart" : v;
                else if (k.Equals("Threshold", StringComparison.OrdinalIgnoreCase)) { int n; if (int.TryParse(v, out n)) MemThreshold = Math.Max(128, Math.Min(65536, n)); }
                else if (k.Equals("Interval", StringComparison.OrdinalIgnoreCase)) { int n; if (int.TryParse(v, out n)) MemInterval = Math.Max(1, Math.Min(1440, n)); }
                else if (k.Equals("Hotkey", StringComparison.OrdinalIgnoreCase)) MemHotkey = v == "1";
                else if (k.StartsWith("TS_", StringComparison.OrdinalIgnoreCase))
                {
                    int n;
                    if (int.TryParse(v, out n) && n >= 0 && n <= 10) SliceRules[k.Substring(3)] = n;
                }
                else if (k.Equals("ISO_MASK", StringComparison.OrdinalIgnoreCase) || k.Equals("ISO_SOFT_GAME", StringComparison.OrdinalIgnoreCase) || k.Equals("ISO_SOFT_ISO", StringComparison.OrdinalIgnoreCase) || k.Equals("IRQ_MASK", StringComparison.OrdinalIgnoreCase))
                {
                    ulong m;
                    if (ulong.TryParse(v, System.Globalization.NumberStyles.HexNumber, null, out m))
                    {
                        if (k.Equals("ISO_MASK", StringComparison.OrdinalIgnoreCase)) IsoMask = m;
                        else if (k.Equals("ISO_SOFT_GAME", StringComparison.OrdinalIgnoreCase)) SoftGameMask = m;
                        else if (k.Equals("ISO_SOFT_ISO", StringComparison.OrdinalIgnoreCase)) SoftIsoMask = m;
                        else IrqMask = m;
                    }
                }
                else if (k.Equals("ISO_MODE", StringComparison.OrdinalIgnoreCase)) IsoSoft = v == "soft" ? 1 : 0;
                else if (k.Equals("IRQ_MODE", StringComparison.OrdinalIgnoreCase) && (v == "follow" || v == "custom")) IrqMode = v;
                else if (k.StartsWith("ISO_", StringComparison.OrdinalIgnoreCase))
                {
                    if (v == "1" || v.Equals("fg", StringComparison.OrdinalIgnoreCase)) IsoGames.Add(k.Substring(4));
                    else if (v.Equals("bg", StringComparison.OrdinalIgnoreCase)) IsoBackgrounds.Add(k.Substring(4));
                }
                else if (k.StartsWith("FC_", StringComparison.OrdinalIgnoreCase) && v.Length >= 1)
                {
                    string num = (v[0] == 'h' || v[0] == 's') ? v.Substring(1) : v;
                    int cn;
                    if (int.TryParse(num, out cn) && cn >= 0 && cn < 64) FcRules[k.Substring(3)] = cn;
                }
            }
            if (IrqMode == null) IrqMode = IrqMask != 0 ? "custom" : "follow";
        }
        catch { }
    }

    public static void SaveKey(string key, string val)
    {
        try
        {
            Directory.CreateDirectory(Dir);
            var lines = new List<string>();
            if (System.IO.File.Exists(File))
                foreach (var l in System.IO.File.ReadAllLines(File))
                    if (!l.TrimStart().StartsWith(key + "=", StringComparison.OrdinalIgnoreCase)) lines.Add(l);
            lines.Add(key + "=" + val);
            System.IO.File.WriteAllLines(File, lines.ToArray());
        }
        catch { }
    }

    public static void DeleteKey(string key)
    {
        try
        {
            if (!System.IO.File.Exists(File)) return;
            var lines = new List<string>();
            foreach (var l in System.IO.File.ReadAllLines(File))
                if (!l.TrimStart().StartsWith(key + "=", StringComparison.OrdinalIgnoreCase)) lines.Add(l);
            System.IO.File.WriteAllLines(File, lines.ToArray());
        }
        catch { }
    }

    static readonly string[] PresetPrefixes = { "TS_", "ISO_", "IRQ_", "FC_" };
    static readonly string[] PresetExacts = { "Mode", "Threshold", "Interval", "Hotkey" };

    public static bool IsPresetKey(string k)
    {
        foreach (var p in PresetPrefixes) if (k.StartsWith(p, StringComparison.OrdinalIgnoreCase)) return true;
        foreach (var e in PresetExacts) if (k.Equals(e, StringComparison.OrdinalIgnoreCase)) return true;
        return false;
    }

    public static bool IsMaskKey(string k)
    {
        return k.Equals("ISO_MASK", StringComparison.OrdinalIgnoreCase) || k.Equals("ISO_SOFT_GAME", StringComparison.OrdinalIgnoreCase)
            || k.Equals("ISO_SOFT_ISO", StringComparison.OrdinalIgnoreCase) || k.Equals("IRQ_MASK", StringComparison.OrdinalIgnoreCase);
    }

    public static ulong MaskValue(string k)
    {
        if (k.Equals("ISO_MASK", StringComparison.OrdinalIgnoreCase)) return IsoMask;
        if (k.Equals("ISO_SOFT_GAME", StringComparison.OrdinalIgnoreCase)) return SoftGameMask;
        if (k.Equals("ISO_SOFT_ISO", StringComparison.OrdinalIgnoreCase)) return SoftIsoMask;
        if (k.Equals("IRQ_MASK", StringComparison.OrdinalIgnoreCase)) return IrqMask;
        return 0;
    }

    public static List<string> ExportPresetLines(PresetScope scope)
    {
        var o = new List<string>
        {
            "Mode=" + MemMode,
            "Threshold=" + MemThreshold,
            "Interval=" + MemInterval,
            "Hotkey=" + (MemHotkey ? "1" : "0"),
            "ISO_MODE=" + (IsoSoft == 1 ? "soft" : "hard"),
            "ISO_MASK=" + IsoMask.ToString("X"),
            "IRQ_MODE=" + (IrqMode ?? "follow")
        };
        if (SoftGameMask != 0) o.Add("ISO_SOFT_GAME=" + SoftGameMask.ToString("X"));
        if (SoftIsoMask != 0) o.Add("ISO_SOFT_ISO=" + SoftIsoMask.ToString("X"));
        if (IrqMask != 0) o.Add("IRQ_MASK=" + IrqMask.ToString("X"));
        foreach (var n in IsoGames) o.Add("ISO_" + n + "=1");
        foreach (var n in IsoBackgrounds) o.Add("ISO_" + n + "=bg");
        foreach (var kv in SliceRules) o.Add("TS_" + kv.Key + "=" + kv.Value);
        foreach (var kv in FcRules) o.Add("FC_" + kv.Key + "=" + kv.Value);
        return o;
    }

    public static int ImportPresetLines(List<string> kv, PresetScope scope)
    {
        try
        {
            Directory.CreateDirectory(Dir);
            var keep = new List<string>();
            if (System.IO.File.Exists(File))
                foreach (var l in System.IO.File.ReadAllLines(File))
                {
                    var t = l.Trim();
                    int eq = t.IndexOf('=');
                    if (eq > 0 && IsPresetKey(t.Substring(0, eq).Trim())) continue;
                    keep.Add(l);
                }
            keep.AddRange(kv);
            System.IO.File.WriteAllLines(File, keep.ToArray());
            ResetRules();
            Load();
            return kv.Count;
        }
        catch { return 0; }
    }

    public static void ResetRules()
    {
        MemMode = "smart"; MemThreshold = 1024; MemInterval = 30; MemHotkey = false;
        SliceRules.Clear(); IsoGames.Clear(); IsoBackgrounds.Clear(); FcRules.Clear();
        IsoMask = 0; IsoSoft = 0; SoftGameMask = 0; SoftIsoMask = 0;
        IrqMode = null; IrqMask = 0;
    }
}

class Engine
{
    public const uint StartValue = 5000, Step = 10, MaxValue = 6000;
    public const double Threshold = 1.4;   // ms：slept > 1.4 即不合格
    public const int TestSeconds = 15;

    public uint AppliedValue;
    public bool Holding;
    readonly long _freq;

    public Engine() { Native.QueryPerformanceFrequency(out _freq); }

    public void Apply(uint v)
    {
        uint got;
        Native.NtSetTimerResolution(v, true, out got);
        AppliedValue = v; Holding = true;
        TimerDog.Arm(this);  // 看门狗：进程事件驱动，被驱动级改回才异值重求（零轮询）
    }

    public void Release()
    {
        if (!Holding) return;
        uint got;
        Native.NtSetTimerResolution(AppliedValue, false, out got);
        Holding = false;
        TimerDog.Disarm();
    }

    // 看门狗重申：异值重求。系统在特定条件下（挂机/游戏会话的电源仲裁）会把请求的效力剥掉
    // 只留注册回显——实测同值释放重求救不回，请求一个不同值再回来才重新注册（2026-08-16 确诊，
    // 依据：自动调优器 5000→5020 逐值请求后 Sleep 2.006→1.013 全面恢复）
    public void Reassert()
    {
        if (!Holding) return;
        uint got;
        uint alt = AppliedValue > Engine.Step * 2 ? AppliedValue - Engine.Step : AppliedValue + Engine.Step;
        Native.NtSetTimerResolution(AppliedValue, false, out got);   // 释放目标值（幂等）
        Native.NtSetTimerResolution(alt, true, out got);             // 请求异值 → 强制新注册
        Native.NtSetTimerResolution(alt, false, out got);            // 释放异值
        Native.NtSetTimerResolution(AppliedValue, true, out got);    // 重求目标值
    }

    public uint CurrentResolution()
    {
        uint mn, mx, cur;
        Native.NtQueryTimerResolution(out mn, out mx, out cur);
        return cur;
    }

    public double SampleOnce()
    {
        long a, b;
        Native.QueryPerformanceCounter(out a);
        Thread.Sleep(1);
        Native.QueryPerformanceCounter(out b);
        return (b - a) * 1000.0 / _freq;
    }

    // 连测 5 次取中位数：免疫采样相位运气+偶发尖峰，且 3/5 多数好才算好
    public double SampleBurst()
    {
        var v = new double[5];
        for (int k = 0; k < 3; k++) v[k] = SampleOnce();
        Array.Sort(v);
        return v[2];
    }
}

// ================= 计时器看门狗（事件驱动，零轮询） =================
// 病（2026-08-24 用户报障）：某些应用退出后全局精度被改回 1.0ms 并保持。根因不在用户态——
// 本机 20348 实测应用 set/release/退出全组合都顶不掉我们持有的值（9 例矩阵）；真凶=应用自带
// 内核驱动卸载时 ExSetTimerResolution 把全局绝对写回它记录的旧值（绕过一切用户态 hook），
// 以及电源仲裁剥请求效力（08-16 已确诊，解药=异值重求 Reassert，当时 30s 巡检版按零周期规矩删过）。
// 药：蹭 EtwProc 共享会话（引用计数，与 Iso/FirstCore 同机制），进程启动/退出后 +3s/+15s
// 各一次去抖检查（驱动卸载可能滞后于进程退出），确认降级才 Reassert。无进程事件=零开销。
static class TimerDog
{
    static Engine _e;
    static bool _armed;
    static int _pending;
    public static event Action<string> Notified;   // 自愈通知（上状态行）

    public static void Arm(Engine e)
    {
        _e = e;
        if (_armed) return;
        if (!EtwProc.Acquire()) { Log("arm: EtwProc 启动失败 " + EtwProc.Error); return; }
        EtwProc.Started += OnStartedFiltered;
        EtwProc.Stopped += OnStoppedFiltered;
        _armed = true;
        Log("armed");
        Kick();   // 启动即自查一次：覆盖"我们启动前已被顶回"的存量场景
    }

    public static void Disarm()
    {
        if (!_armed) return;
        _armed = false; _e = null;
        EtwProc.Started -= OnStartedFiltered;
        EtwProc.Stopped -= OnStoppedFiltered;
        EtwProc.Release();
    }

    static void Kick()
    {
        if (System.Threading.Interlocked.Exchange(ref _pending, 1) != 0) return;   // 15s 窗口内的事件合并
        Once(3000, () => Check("+3s"));
        Once(15000, () => { _pending = 0; Check("+15s"); });
    }

    // 一次性延时（非轮询：单次触发即销毁）
    static void Once(int ms, Action a)
    {
        System.Threading.Timer t = null;
        t = new System.Threading.Timer(_ => { try { a(); } catch { } try { t.Dispose(); } catch { } }, null, ms, Timeout.Infinite);
    }

    static DateTime _suppressUntil = DateTime.MinValue;   // 重申无效冷却截止（见下）
    public static Func<bool> DriverFallback;   // 全局复检仍超标时调用（SuiteApp 注入）：true=内核驱动兜底已启用
    static volatile int _probePid;   // 进行中的全局探针子进程：其启停事件不 Kick（防探针→事件→Check→探针递归）

    static void OnStartedFiltered(int pid, string name) { if (pid != _probePid) Kick(); }
    static void OnStoppedFiltered(int pid) { if (pid != _probePid) Kick(); }

    // 全局效力真判据：起无请求子进程实测 Sleep(1)（见 SleepSampleCli 注释）。失败返回 0=按正常处理（fail-open，不误起驱动）。
    static double GlobalSleepProbe()
    {
        string tmp = Path.Combine(Path.GetTempPath(), "dunsuitelite_probe.txt");
        try { File.Delete(tmp); } catch { }
        try
        {
            var p = Process.Start(new ProcessStartInfo
            {
                FileName = System.Reflection.Assembly.GetExecutingAssembly().Location,
                Arguments = "-sleepsample \"" + tmp + "\"",
                CreateNoWindow = true, UseShellExecute = false, WindowStyle = ProcessWindowStyle.Hidden
            });
            if (p == null) return 0;
            _probePid = p.Id;
            p.WaitForExit(4000);
            ClearProbePidDelayed();
            double ms;
            if (double.TryParse(File.ReadAllText(tmp), out ms)) return ms;
        }
        catch { ClearProbePidDelayed(); }
        return 0;
    }

    // 延迟清零探针 pid：ETW 启停事件异步投递晚到，立即清零会漏过滤→探针自身事件 Kick 下一轮，
    // 形成 15s 合并窗+~2s 探针寿命=17s 整的自维持循环（全机器每 17s 白起两个子进程，本不该有任何周期活动）
    static void ClearProbePidDelayed()
    {
        int done = _probePid;
        if (done != 0) Once(5000, () => { if (_probePid == done) _probePid = 0; });   // ==done 守卫：HEAL 连续两探针时防旧回调误清新的
    }

    static void Check(string tag)
    {
        var e = _e;
        if (!_armed || e == null || !e.Holding) return;
        if (DateTime.Now < _suppressUntil) { Log("check " + tag + " suppressed"); return; }
        uint before = e.CurrentResolution();
        bool degraded = before > e.AppliedValue + 200;   // 查询可见的变粗（容差 0.02ms）
        double slept = 0, gSlept = 0;
        if (!degraded) { slept = e.SampleBurst(); degraded = slept > Engine.Threshold; }   // 查询会撒谎（电源仲裁只剥效力留回显）：实测才准
        if (!degraded) { gSlept = GlobalSleepProbe(); degraded = gSlept > Engine.Threshold; }   // 自身正常≠全局正常（22H2：自身请求仅对己有效，全局仍 15.6）——无请求子进程才是真判据
        if (degraded)
        {
            e.Reassert();
            uint after = e.CurrentResolution();
            double sleptAfter = e.SampleBurst();
            double gAfter = GlobalSleepProbe();
            Log(string.Format("HEAL {0}: query {1}→{2}, slept {3:F3}→{4:F3}ms, global {5:F2}→{6:F2}ms (holding {7})", tag, before, after, slept, sleptAfter, gSlept, gAfter, e.AppliedValue));
            if (sleptAfter <= Engine.Threshold && gAfter > Engine.Threshold)
            {
                // 自身治愈但全局仍粗 = 22H2 型（用户态请求无全局效力，Reassert 治不了）→ 内核驱动兜底（只兜一次）
                var fb = DriverFallback;
                if (fb != null && fb())
                {
                    Log("全局无效（global " + gAfter.ToString("F1") + "ms），内核驱动兜底已启用");
                    var h2 = Notified;
                    if (h2 != null) h2("本系统需内核级解锁，已自动启用");
                    return;
                }
                _suppressUntil = DateTime.Now.AddMinutes(10);
                Log("全局无效且驱动兜底无果（装不上/已兜过），冷却 10 分钟");
                return;
            }
            if (sleptAfter > Engine.Threshold)
            {
                // 重申后自身实测仍超标 = 负载调度噪声/别人持更细的锁（如三角洲 0.5）——20348 按进程记账，
                // 别人持有的值顶不动，重申只会随进程事件无限空转：冷却 10 分钟。
                // 真精度丢失（电源仲裁/驱动写回）重申后 sleptAfter 会回落（08-16 实测 2.006→1.013），不进此分支。
                _suppressUntil = DateTime.Now.AddMinutes(10);
                Log("heal 无效（非精度丢失），冷却 10 分钟");
                return;   // 不上状态行：没修任何东西，报"已重新锁定"是假话
            }
            var h = Notified;
            if (h != null) h(string.Format("计时器被改回 {0:F4}ms，已重新锁定 {1:F4}ms", before / 10000.0, e.AppliedValue / 10000.0));
        }
        else Log("check " + tag + " ok (query " + before + ")");
    }

    static void Log(string s)
    {
        try { File.AppendAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_heal.log"), DateTime.Now.ToString("MM-dd HH:mm:ss.fff ") + s + "\r\n"); } catch { }
    }
}

// ================= 自动调优状态机 =================
class AutoTuner
{
    readonly Engine _e;
    readonly Action<string> _log;
    readonly Action<uint, uint, double> _stats;
    readonly Action<int, int> _progress;
    readonly Action<string> _status;
    public event Action<bool, uint, uint> Finished;
    CancellationTokenSource _cts;
    bool _running;

    public AutoTuner(Engine e, Action<string> log, Action<uint, uint, double> stats,
        Action<int, int> progress, Action<string> status)
    {
        _e = e; _log = log ?? (s => { });
        _stats = stats ?? ((a, b, c) => { });
        _progress = progress ?? ((a, b) => { });
        _status = status ?? (s => { });
    }

    public bool Running { get { return _running; } }

    public void RunAsync()
    {
        if (_running) return;
        _running = true;
        _cts = new CancellationTokenSource();
        var ct = _cts.Token;
        Task.Run(() =>
        {
            try { Run(ct); }
            catch (OperationCanceledException) { _status("已停止"); }
            finally { _running = false; }
        });
    }

    public void Stop() { if (_cts != null) _cts.Cancel(); }

    void Run(CancellationToken ct)
    {
        uint v = Engine.StartValue;
        uint lastTested = 0;
        while (true)
        {
            ct.ThrowIfCancellationRequested();
            _e.Apply(v);
            _status("设定 " + v + " 中…");
            _stats(v, 0, 0);
            Thread.Sleep(1000);
            _e.SampleOnce();                       // 暖机1（刚改完有跳动，丢弃）
            Thread.Sleep(1000);
            _e.SampleOnce();                       // 暖机2（多观测1-2秒）
            ct.ThrowIfCancellationRequested();
            uint r = _e.CurrentResolution();
            _stats(v, r, 0);
            _log(string.Format("set {0} -> res {1:F4}ms", v, r / 10000.0));

            if (r == lastTested)
            {
                _status(string.Format("设定 {0} → Resolution {1:F4}ms 未变化，跳过测试，继续 +{2}", v, r / 10000.0, Engine.Step));
                Thread.Sleep(600);
            }
            else
            {
                lastTested = r;
                bool pass = true;
                int bad = 0;
                for (int i = 1; i <= Engine.TestSeconds; i++)
                {
                    ct.ThrowIfCancellationRequested();
                    // 先测量再更新 UI：采样前任何多余工作都会让 Sleep(1) 错过 tick 对齐窗口
                    double slept = _e.SampleBurst();   // 连测5次取中位：免疫相位运气+单点尖峰
                    bool observe = i <= 2;   // 前 2 秒观察期（换档瞬态，不判定）
                    _status(string.Format(observe ? "设定 {0}（{1:F4}ms）观察中 {2}/2" : "设定 {0}（{1:F4}ms）判定中 {2}/{3}",
                        v, r / 10000.0, observe ? i : i - 2, Engine.TestSeconds - 2));
                    _log("  #" + i + (observe ? " obs" : " judge") + " burst-med " + slept.ToString("F4"));
                    _stats(v, r, slept);
                    _progress(i, Engine.TestSeconds);
                    if (!observe && slept > Engine.Threshold)
                    {
                        bad++;
                        if (bad >= 2) { pass = false; break; }   // 允许 1 次系统噪声尖峰，2 次才判失败
                    }
                    Thread.Sleep(1000);   // 与 MeasureSleep 相同的 1000ms 采样节拍
                }
                _progress(0, Engine.TestSeconds);
                if (pass)
                {
                    _status("设定完成");
                    if (Finished != null) Finished(true, v, r);
                    return;
                }
                _status(string.Format("设定 {0} 未通过（slept > 1.4ms），增加数值", v));
            }

            v += Engine.Step;
            if (v > Engine.MaxValue)
            {
                _status("已达上限 " + Engine.MaxValue + "，未通过");
                if (Finished != null) Finished(false, v - Engine.Step, lastTested);
                return;
            }
        }
    }
}

// ================= 游戏负载模拟（突发波动型） =================
class GameLoad
{
    volatile bool _run;
    readonly List<Thread> _threads = new List<Thread>();

    public void Start()
    {
        if (_run) return;
        _run = true;
        for (int t = 0; t < 2; t++)
        {
            var th = new Thread(Loop) { IsBackground = true };
            _threads.Add(th);
            th.Start();
        }
    }

    public void Stop() { _run = false; }

    void Loop()
    {
        var rnd = new Random(Environment.TickCount + Thread.CurrentThread.ManagedThreadId * 7919);
        long freq, t0, t1;
        Native.QueryPerformanceFrequency(out freq);
        double x = 0;
        while (_run)
        {
            int workMs = rnd.Next(30, 160);          // 突发工作 30-160ms
            Native.QueryPerformanceCounter(out t0);
            do
            {
                for (int i = 0; i < 5000; i++) x += Math.Sqrt(x + 1.1);   // 轻量浮点压力
                Native.QueryPerformanceCounter(out t1);
            } while ((t1 - t0) * 1000.0 / freq < workMs && _run);
            Thread.Sleep(rnd.Next(40, 350));          // 空闲 40-350ms，忽高忽低
        }
    }
}

// ================= DPC 延迟引擎（直接驱动通信，无外部进程） =================
class DpcEngine
{
    public const uint IOCTL_CAPS = 0x81772004;
    public const uint IOCTL_START = 0x81772008;
    public const uint IOCTL_STOP = 0x8177200c;
    public const uint IOCTL_STATS = 0x81772010;
    public const uint IOCTL_RESET = 0x81772014;
    const string ServiceName = "DunSuiteLiteDpc";

    IntPtr _h = Native.InvalidHandle, _svc, _scm;
    public bool Ok;
    public string Error = "";
    public uint ActiveIntervalUs;   // 实际生效的采样间隔（请求值≠生效值时=驱动钳制后的值）
    public bool StreamOffActive;    // 零流实验中：START 后已立即 STOP（流停、服务保留）

    // streamOff=true（实验）：START 后立即 IOCTL_STOP 停 DPC 流但保留服务/句柄——
    // 若请求持有与流解耦则=真·零检测解锁（用户 22H2 实测验证项）
    public bool Start(uint intervalUs, bool streamOff)
    {
        return StartCore(intervalUs, streamOff);
    }

    public static string DataDir
    {
        get
        {
            string d = Cfg.Dir;
            Directory.CreateDirectory(d);
            return d;
        }
    }

    static string ExtractDriver()
    {
        string dst = Path.Combine(DataDir, "dpclat_x64.sys");
        using (var s = Assembly.GetExecutingAssembly().GetManifestResourceStream("dpc.sys"))
        {
            if (s == null) throw new Exception("内嵌驱动资源缺失");
            if (!File.Exists(dst) || new FileInfo(dst).Length != s.Length)
                using (var fs = File.Create(dst)) s.CopyTo(fs);
        }
        return dst;
    }

    bool StartCore(uint intervalUs, bool streamOff)
    {
        Stop();
        try
        {
            string sysPath = ExtractDriver();
            _scm = Native.OpenSCManager(null, null, 0xF003F);
            if (_scm == IntPtr.Zero) throw new Exception("OpenSCManager: " + Marshal.GetLastWin32Error());
            _svc = Native.OpenService(_scm, ServiceName, 0xF01FF);
            if (_svc == IntPtr.Zero)
                _svc = Native.CreateService(_scm, ServiceName, ServiceName, 0xF01FF, 1, 3, 0, sysPath, null, IntPtr.Zero, null, null, null);
            if (_svc == IntPtr.Zero) throw new Exception("CreateService: " + Marshal.GetLastWin32Error());
            if (!Native.StartService(_svc, 0, IntPtr.Zero))
            {
                int e = Marshal.GetLastWin32Error();
                if (e != 1056 && !OpenDevice()) // 1056 = 已在运行
                    throw new Exception("StartService: " + e);
            }
            if (_h == Native.InvalidHandle && !OpenDevice())
                throw new Exception("OpenDevice: " + Marshal.GetLastWin32Error());

            uint ret;
            byte[] inBuf = BitConverter.GetBytes(intervalUs);
            byte[] outBuf = new byte[4];
            // DPC 落核控制：Win8+ 定时器入武装时所在核的定时器表，周期 DPC 固定打在该核——随机落核可能砸中
            // 游戏渲染/输入线程或外设中断所在核（08-28 用户机器实锤链：驱动全核随机武装→人物移动模型抖；
            // 手感好的五天=开机武装那次落了好核）。有隔离配置=隔离区即非前台区（取区首核）；
            // 无=末逻辑核（CPU0 传统 IRQ 最挤，末核通常最闲）。只钉武装这一下，IOCTL 后立即还原。
            bool begAff = false, affPinned = false;
            IntPtr prevAff = IntPtr.Zero;
            try
            {
                ulong pin, pinGame;
                Iso.Zones(out pin, out pinGame);   // 当前模式隔离区
                if (pin != 0) pin = pin & (~pin + 1);   // 取最低置位=区首核
                else pin = 1UL << (Environment.ProcessorCount - 1);
                Thread.BeginThreadAffinity(); begAff = true;
                prevAff = Native.SetThreadAffinityMask(Native.GetCurrentThread(), new IntPtr((long)pin));
                affPinned = prevAff != IntPtr.Zero;
                if (!Native.DeviceIoControl(_h, IOCTL_START, inBuf, 4, outBuf, 4, out ret, IntPtr.Zero))
                    throw new Exception("IOCTL_START: " + Marshal.GetLastWin32Error());
            }
            finally
            {
                if (affPinned) { try { Native.SetThreadAffinityMask(Native.GetCurrentThread(), prevAff); } catch { } }
                if (begAff) { try { Thread.EndThreadAffinity(); } catch { } }
            }
            if (streamOff)
            {
                // 零流实验：立即停 DPC 流，服务/句柄/请求持有保留
                uint r2; Native.DeviceIoControl(_h, IOCTL_STOP, null, 0, null, 0, out r2, IntPtr.Zero);
                StreamOffActive = true;
            }
            Ok = true; Error = "";
            ActiveIntervalUs = intervalUs;
            if (intervalUs != 1000 && !streamOff)   // 停流后 STATS 语义未知，跳过回读校验
            {
                // 驱动是签名二进制无源码，传参语义只能回读验证：interval 回显≠请求值=不认大间隔 → 回退现状 1ms
                uint iv, mn, mx, av;
                if (GetStats(out iv, out mn, out mx, out av) && iv != intervalUs)
                {
                    Stop();
                    return StartCore(1000, false);
                }
            }
        }
        catch (Exception ex) { Error = ex.Message; Ok = false; }
        return Ok;
    }

    // 旧版非正常退出会残留 RUNNING 的孤儿驱动（08-16 实证"taskkill 后驱动留在内核"）；按需版有效机器
    // 不再碰驱动=孤儿会永久滞留空转。探针判定不需要驱动时顺带清理：服务存在且非本进程持有 → 停+删。
    public static void CleanupOrphan()
    {
        try
        {
            IntPtr scm = Native.OpenSCManager(null, null, 0xF003F);
            if (scm == IntPtr.Zero) return;
            IntPtr svc = Native.OpenService(scm, ServiceName, 0xF01FF);
            if (svc != IntPtr.Zero)
            {
                Native.SERVICE_STATUS ss;
                Native.ControlService(svc, 1, out ss);
                Native.DeleteService(svc);
                Native.CloseServiceHandle(svc);
            }
            Native.CloseServiceHandle(scm);
        }
        catch { }
    }

    bool OpenDevice()
    {
        _h = Native.CreateFile(@"\\.\dpclat_static_device", 0xC0000000, 3, IntPtr.Zero, 3, 0, IntPtr.Zero);
        return _h != Native.InvalidHandle;
    }

    public bool GetStats(out uint interval, out uint min, out uint max, out uint avg)
    {
        interval = min = max = avg = 0;
        if (!Ok || _h == Native.InvalidHandle) return false;
        uint ret;
        byte[] inBuf = new byte[20];
        byte[] outBuf = new byte[20];
        if (!Native.DeviceIoControl(_h, IOCTL_STATS, inBuf, 20, outBuf, 20, out ret, IntPtr.Zero))
        { Ok = false; return false; }
        interval = BitConverter.ToUInt32(outBuf, 0);
        min = BitConverter.ToUInt32(outBuf, 4);
        max = BitConverter.ToUInt32(outBuf, 8);
        avg = BitConverter.ToUInt32(outBuf, 12);
        return true;
    }

    public void ResetStats()
    {
        if (!Ok || _h == Native.InvalidHandle) return;
        uint ret;
        Native.DeviceIoControl(_h, IOCTL_RESET, null, 0, null, 0, out ret, IntPtr.Zero);
    }

    public void Stop()
    {
        try
        {
            if (_h != Native.InvalidHandle)
            {
                uint ret;
                Native.DeviceIoControl(_h, IOCTL_STOP, null, 0, null, 0, out ret, IntPtr.Zero);
                Native.CloseHandle(_h);
                _h = Native.InvalidHandle;
            }
            if (_svc != IntPtr.Zero)
            {
                Native.SERVICE_STATUS ss;
                Native.ControlService(_svc, 1, out ss);
                Native.DeleteService(_svc);
                Native.CloseServiceHandle(_svc);
                _svc = IntPtr.Zero;
            }
            if (_scm != IntPtr.Zero) { Native.CloseServiceHandle(_scm); _scm = IntPtr.Zero; }
        }
        catch { }
        Ok = false;
        StreamOffActive = false;
    }
}

// ================= DPC 竖条图 =================
class DpcGraph : FrameworkElement
{
    readonly Queue<double> _samples = new Queue<double>();
    double _scale = 500;   // µs 纵轴上限，自适应（显示值已减周期）

    public void Push(double v)
    {
        _samples.Enqueue(v);
        while (_samples.Count > 240) _samples.Dequeue();
        if (v > _scale) _scale = v * 1.2;
        else if (_scale > 500 && v < _scale * 0.5) _scale = Math.Max(500, _scale * 0.98);
        InvalidateVisual();
    }

    protected override void OnRender(DrawingContext dc)
    {
        double w = ActualWidth, h = ActualHeight;
        if (w < 10 || h < 10) return;
        dc.DrawRectangle(new SolidColorBrush(Color.FromRgb(0xFA, 0xFA, 0xFA)), null, new Rect(0, 0, w, h));

        // 500µs 参考线（DPC Latency Checker 警戒线）
        if (_scale > 500)
        {
            var refPen = new Pen(new SolidColorBrush(Color.FromRgb(0xE3, 0xE3, 0xE3)), 1);
            refPen.Freeze();
            double y = h - 500.0 / _scale * h;
            dc.DrawLine(refPen, new Point(0, y), new Point(w, y));
        }

        if (_samples.Count == 0) return;
        const double barW = 2.0, gap = 1.2;
        double step = barW + gap;
        int maxBars = (int)(w / step);
        var arr = _samples.ToArray();
        int n = Math.Min(arr.Length, maxBars);
        var brush = new SolidColorBrush(Color.FromRgb(0x11, 0x11, 0x11));
        brush.Freeze();
        var dimBrush = new SolidColorBrush(Color.FromRgb(0x88, 0x88, 0x88));
        dimBrush.Freeze();
        for (int i = 0; i < n; i++)
        {
            double v = arr[arr.Length - 1 - i];          // 最新在右
            double bh = Math.Max(1.0, Math.Min(v, _scale) / _scale * h);
            double x = w - (i + 1) * step;
            dc.DrawRectangle(i < n / 3 ? brush : dimBrush, null, new Rect(x, h - bh, barW, bh));
        }
    }
}

// ================= CPU 时间片（Job Object SchedulingClass，复刻来掌芯专业版） =================
// 原理：Windows 没有直接设进程调度类的公开 API，只能挂在 Job Object 上：
//   JOBOBJECT_BASIC_LIMIT_INFORMATION.SchedulingClass (0-9) + 标志 0x80，
//   Job 内所有进程的所有线程统一按该值加权量子长度。6-9 档需 SeIncreaseBasePriorityPrivilege。
// Job 复用 = 常驻句柄缓存（命名 Job "Local\DunSuiteLiteTS_<pid>" 仅作调试标识）。
// 效果存续：我们退出后档位仍生效到目标退出（成员引用保住 Job），但句柄缓存随进程消失，
//   下次启动对仍在跑的目标会重建一层嵌套 Job（同档值无害）。
// 注意：x64 结构体 64 字节（SchedulingClass@60）；来掌芯抓到的 48 字节是 x86/WoW64 布局。
static class Slice
{
    public static readonly string[] LevelNames = { "忽略", "极长", "很长", "中长", "略长", "标准", "略短", "中短", "较短", "很短", "极短" };
    static readonly int[] LevelClass = { -1, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0 };   // 忽略=-1（不调用/清除）

    [StructLayout(LayoutKind.Sequential)]
    struct JobBasicLimit
    {
        public long PerProcessUserTimeLimit;   // +0
        public long PerJobUserTimeLimit;       // +8
        public uint LimitFlags;                // +16
        public UIntPtr MinimumWorkingSetSize;  // +24 (x64)
        public UIntPtr MaximumWorkingSetSize;  // +32
        public uint ActiveProcessLimit;        // +40
        public UIntPtr Affinity;               // +48
        public uint PriorityClass;             // +56
        public uint SchedulingClass;           // +60
    }
    const uint LIMIT_SCHEDULING_CLASS = 0x80;
    const int JobBasicLimitInfo = 2;

    [DllImport("kernel32.dll", SetLastError = true, CharSet = CharSet.Unicode)] static extern IntPtr CreateJobObject(IntPtr sa, string name);
    [DllImport("kernel32.dll", SetLastError = true)] static extern bool IsProcessInJob(IntPtr proc, IntPtr job, out bool inJob);
    [DllImport("kernel32.dll", SetLastError = true)] static extern bool AssignProcessToJobObject(IntPtr job, IntPtr proc);
    [DllImport("kernel32.dll", SetLastError = true)] static extern bool SetInformationJobObject(IntPtr job, int cls, IntPtr info, uint len);
    [DllImport("kernel32.dll", SetLastError = true)] static extern bool QueryInformationJobObject(IntPtr job, int cls, IntPtr info, uint len, IntPtr retLen);
    [DllImport("kernel32.dll", SetLastError = true)] static extern IntPtr OpenProcess(uint access, bool inherit, int pid);
    [DllImport("kernel32.dll", SetLastError = true)] static extern bool CloseHandle(IntPtr h);

    static string JobName(int pid) { return "Local\\DunSuiteLiteTS_" + pid; }

    // pid → 我们持有的 job 句柄。必须常驻持有：命名对象在最后句柄关闭时名字即被摘除
    // （对象本体因成员引用还在、档位继续生效，但永远无法再按名打开——2026-08-16 实测 OpenJobObject:2）。
    static readonly Dictionary<int, IntPtr> _jobs = new Dictionary<int, IntPtr>();

    public static string LastQueryError = "";

    // 缓存有效性校验：目标死了或 PID 复用（已不在该 job 里）→ 回收句柄，返回 false
    static bool CheckCached(int pid, out IntPtr job)
    {
        if (!_jobs.TryGetValue(pid, out job)) return false;
        IntPtr q = OpenProcess(0x400, false, pid);   // QUERY_INFORMATION
        bool inJob = false, alive = q != IntPtr.Zero;
        if (alive) { IsProcessInJob(q, job, out inJob); CloseHandle(q); }
        if (!alive || !inJob) { CloseHandle(job); _jobs.Remove(pid); job = IntPtr.Zero; return false; }
        return true;
    }

    // 查询我们缓存 Job 里该进程的当前档；inOurJob=false 表示本次运行没管过它
    public static int QueryClass(int pid, out bool inOurJob)
    {
        inOurJob = false;
        LastQueryError = "";
        IntPtr job;
        if (!CheckCached(pid, out job)) return -1;
        IntPtr buf = Marshal.AllocHGlobal(64);
        try
        {
            for (int k = 0; k < 64; k += 8) Marshal.WriteInt64(buf, k, 0);
            if (!QueryInformationJobObject(job, JobBasicLimitInfo, buf, 64, IntPtr.Zero))
            { LastQueryError = "Query:" + Marshal.GetLastWin32Error(); return -1; }
            uint flags = (uint)Marshal.ReadInt32(buf, 16);
            uint sc = (uint)Marshal.ReadInt32(buf, 60);
            inOurJob = true;
            if ((flags & LIMIT_SCHEDULING_CLASS) == 0) return -1;
            return (int)sc;
        }
        finally { Marshal.FreeHGlobal(buf); }
    }

    public static void CloseAll()
    {
        foreach (var kv in _jobs) CloseHandle(kv.Value);
        _jobs.Clear();
    }

    // sc: -1=清除标志（忽略档） 0-9=设定
    public static string ApplyClass(int pid, int sc)
    {
        int idx = 0;
        if (sc >= 0)
        {
            idx = -1;
            for (int k = 1; k < LevelClass.Length; k++) if (LevelClass[k] == sc) { idx = k; break; }
            if (idx < 0) return "FAIL bad class";
        }
        return Apply(pid, idx);
    }

    // levelIdx: 0=忽略（清除标志） 1..10=设定 LevelNames 对应档
    public static string Apply(int pid, int levelIdx)
    {
        if (levelIdx < 0 || levelIdx > 10) return "FAIL bad level";
        int sc = LevelClass[levelIdx];
        if (sc >= 6) SuiteApp.EnablePrivilege("SeIncreaseBasePriorityPrivilege");
        IntPtr proc = IntPtr.Zero, job = IntPtr.Zero;
        try
        {
            if (!CheckCached(pid, out job))   // 缓存命中且成员有效=复用；失效已回收
            {
                if (levelIdx == 0) return "忽略";   // 没我们的 Job，忽略=无操作
                proc = OpenProcess(0x100 | 0x400 | 0x1, false, pid);   // SET_QUOTA|QUERY_INFORMATION|TERMINATE（Assign 必须要 TERMINATE=0x1）
                if (proc == IntPtr.Zero) return "FAIL OpenProcess:" + Marshal.GetLastWin32Error();
                job = CreateJobObject(IntPtr.Zero, JobName(pid));
                if (job == IntPtr.Zero) return "FAIL CreateJobObject:" + Marshal.GetLastWin32Error();
                if (!AssignProcessToJobObject(job, proc))
                {
                    string fail = "FAIL Assign:" + Marshal.GetLastWin32Error();   // 5=目标在受限 Job/保护进程
                    CloseHandle(job);
                    return fail;
                }
                _jobs[pid] = job;   // 常驻持有：句柄全关会导致名字摘除无法再复用
            }
            IntPtr buf = Marshal.AllocHGlobal(64);
            try
            {
                // 读当前限制 → 只改 SchedulingClass/flags 保留其他 → 写回 → 读回验证
                for (int k = 0; k < 64; k += 8) Marshal.WriteInt64(buf, k, 0);
                if (!QueryInformationJobObject(job, JobBasicLimitInfo, buf, 64, IntPtr.Zero))
                    return "FAIL Query:" + Marshal.GetLastWin32Error();
                uint flags = (uint)Marshal.ReadInt32(buf, 16);
                if (levelIdx == 0) flags &= ~LIMIT_SCHEDULING_CLASS;
                else flags |= LIMIT_SCHEDULING_CLASS;
                Marshal.WriteInt32(buf, 16, (int)flags);
                if (levelIdx != 0) Marshal.WriteInt32(buf, 60, sc);
                if (!SetInformationJobObject(job, JobBasicLimitInfo, buf, 64))
                    return "FAIL Set:" + Marshal.GetLastWin32Error();
                // 读回验证（flags + 值双核对，与复刻文档一致）
                for (int k = 0; k < 64; k += 8) Marshal.WriteInt64(buf, k, 0);
                if (QueryInformationJobObject(job, JobBasicLimitInfo, buf, 64, IntPtr.Zero))
                {
                    uint cf = (uint)Marshal.ReadInt32(buf, 16);
                    uint cs = (uint)Marshal.ReadInt32(buf, 60);
                    if (levelIdx == 0)
                        return (cf & LIMIT_SCHEDULING_CLASS) == 0 ? "已清除" : "FAIL 清除验证 flags=0x" + cf.ToString("X");
                    if ((cf & LIMIT_SCHEDULING_CLASS) != 0 && cs == (uint)sc) return "OK";
                    return "FAIL 读回验证 flags=0x" + cf.ToString("X") + " sc=" + cs;
                }
                return "OK(unverified)";
            }
            finally { Marshal.FreeHGlobal(buf); }
        }
        finally
        {
            if (proc != IntPtr.Zero) CloseHandle(proc);   // job 句柄留在缓存里不关
        }
    }
}

// ================= CPU 拓扑（物理核心/SMT 分组 + L3 缓存组=CCD / Intel 大小核=P·E 组） =================
// 实测 9950X3D：16 物理核（核 i=CPU 2i/2i+1，SMT 成对）；CCD0=CPU0-15 L3 96MB（3D V-Cache），
// CCD1=CPU16-31 L3 32MB。CCD 分组依据=共享 L3（RelationCache Level3+Unified），X3D 两个 L3 不等大，
// 大的标 3D 缓存。>64 逻辑处理器（多处理器组）不支持。
// Intel 混合架构（12 代起）：L3 全核共享只有一条，分不了组——改按 RelationProcessorCore 的
// EfficiencyClass（@9，非混合全为 0）分组：≥2 种效率级=Hybrid，最高级=P 核（排最前），其余=E 核。
// 老 CPU/AMD 效率级全 0 → 仍走 L3 分组，行为与旧版完全一致。
static class Topo
{
    public class CoreInfo { public ulong Mask; public int Ccd; public byte Eff; }   // Mask=SMT 兄弟对（逻辑 CPU 位）；Eff=效率级
    public class CcdInfo { public ulong Mask; public uint L3MB; public bool VCache; public bool IsP; }   // IsP=混合架构性能核组
    public static readonly List<CoreInfo> Cores = new List<CoreInfo>();
    public static readonly List<CcdInfo> Ccds = new List<CcdInfo>();
    public static ulong AllMask;
    public static int LogicalCount;
    public static bool Supported;
    public static bool Hybrid;   // Intel 大小核模式（分组=效率级而非 L3）

    // 分组显示名（UI 行标签 + 诊断 dump 共用）
    public static string CcdLabel(int c)
    {
        var d = Ccds[c];
        if (Hybrid) return d.IsP ? "P-Core · 性能核" : "E-Core · 能效核";
        if (Ccds.Count > 1) return "CCD" + c + " · L3 " + d.L3MB + "MB" + (d.VCache ? " · 3D缓存" : "");
        return d.L3MB > 0 ? ("L3 " + d.L3MB + "MB") : "全部核心";
    }
    static bool _detected;

    public static void Detect()
    {
        if (_detected) return;
        _detected = true;
        try
        {
            LogicalCount = Environment.ProcessorCount;
            if (LogicalCount > 64 || LogicalCount < 2) return;
            AllMask = LogicalCount >= 64 ? ulong.MaxValue : ((1UL << LogicalCount) - 1);

            var cores = new List<KeyValuePair<ulong, byte>>();
            foreach (var buf in EnumInfo(0))   // RelationProcessorCore
            {
                if (Marshal.ReadInt16(buf, 40) != 0) continue;   // 只支持处理器组 0
                cores.Add(new KeyValuePair<ulong, byte>((ulong)Marshal.ReadInt64(buf, 32), Marshal.ReadByte(buf, 9)));   // Mask @32, EfficiencyClass @9
            }
            var l3 = new List<KeyValuePair<ulong, uint>>();
            foreach (var buf in EnumInfo(2))   // RelationCache
            {
                if (Marshal.ReadByte(buf, 8) != 3) continue;     // Level=3
                if (Marshal.ReadInt32(buf, 16) != 0) continue;   // Type=CacheUnified(0)
                l3.Add(new KeyValuePair<ulong, uint>((ulong)Marshal.ReadInt64(buf, 40), (uint)Marshal.ReadInt32(buf, 12)));
            }
            var effs = new List<byte>();
            foreach (var co in cores) if (!effs.Contains(co.Value)) effs.Add(co.Value);
            effs.Sort();
            Hybrid = effs.Count >= 2;
            if (Hybrid)   // Intel 大小核：L3 全共享，按效率级分组（最高级=P 核排最前）
            {
                uint sharedL3 = 0;
                foreach (var kv in l3) sharedL3 += kv.Value;
                for (int e = effs.Count - 1; e >= 0; e--)
                {
                    ulong gm = 0;
                    foreach (var co in cores) if (co.Value == effs[e]) gm |= co.Key;
                    Ccds.Add(new CcdInfo { Mask = gm, L3MB = sharedL3 / 1048576, IsP = e == effs.Count - 1 });
                }
                for (int i = 0; i < cores.Count; i++)
                    Cores.Add(new CoreInfo { Mask = cores[i].Key, Eff = cores[i].Value, Ccd = effs.Count - 1 - effs.IndexOf(cores[i].Value) });
            }
            else   // AMD/老 Intel：共享 L3 分组（原有逻辑）
            {
                uint maxL3 = 0;
                foreach (var kv in l3) maxL3 = Math.Max(maxL3, kv.Value);
                foreach (var kv in l3)
                    Ccds.Add(new CcdInfo { Mask = kv.Key, L3MB = kv.Value / 1048576, VCache = l3.Count > 1 && kv.Value == maxL3 });
                for (int i = 0; i < cores.Count; i++)
                {
                    int ccd = 0;
                    for (int c = 0; c < Ccds.Count; c++)
                        if ((cores[i].Key & Ccds[c].Mask) == cores[i].Key) { ccd = c; break; }
                    Cores.Add(new CoreInfo { Mask = cores[i].Key, Eff = cores[i].Value, Ccd = ccd });
                }
            }
            if (Cores.Count == 0) return;
            if (Ccds.Count == 0)   // 无 L3 信息（老 CPU）：合成一个全覆盖伪 CCD 保证 UI 能出框
                Ccds.Add(new CcdInfo { Mask = AllMask, L3MB = 0, VCache = false });
            Supported = true;
        }
        catch { }
    }

    static IEnumerable<IntPtr> EnumInfo(int rel)
    {
        uint len = 0;
        Native.GetLogicalProcessorInformationEx(rel, IntPtr.Zero, ref len);
        if (len == 0) yield break;
        IntPtr p = Marshal.AllocHGlobal((int)len);
        try
        {
            if (!Native.GetLogicalProcessorInformationEx(rel, p, ref len)) yield break;
            long off = 0;
            while (off < len)
            {
                IntPtr cur = new IntPtr(p.ToInt64() + off);
                uint size = (uint)Marshal.ReadInt32(cur, 4);
                if (size == 0) break;
                yield return cur;   // 消费方在枚举期间即读值，p 存活（finally 在枚举结束后才跑）
                off += size;
            }
        }
        finally { Marshal.FreeHGlobal(p); }
    }
}

// ================= ETW 进程事件（零轮询：内核主动推送进程创建/退出） =================
// 通道：私有实时会话 + Microsoft-Windows-Kernel-Process（WINEVENT_KEYWORD_PROCESS=0x10）。
// 20348 实测：start=opcode 1 / stop=opcode 2；ProcessID+ImageName 用 TDH 按名解码（ImageName=设备全路径，
// stop 事件的名字段是垃圾——stop 只按 PID 匹配）。三个实测坑：①EVENT_TRACE_LOGFILE.EventRecordCallback
// 在 x64 偏移 424（zig cc offsetof 实证，手推错过两次）②ControlTrace 停止码=1（0=查询）③FlushTimer
// 必须 ≥1s，否则低频事件滞留缓冲不投递。
static class EtwProc
{
    public static event Action<int, string> Started;   // (pid, 内核设备全路径)
    public static event Action<int> Stopped;           // (pid)
    public static string Error = "";

    static readonly Guid KernelProcess = new Guid("22FB2CD6-0E7B-422B-A0C7-2FAD1FD0E716");
    const string SessionName = "DunSuiteLite-Process";
    static ulong _session, _trace;
    static Thread _thread;
    static volatile bool _stop;
    static bool _running;
    static readonly object _sync = new object();

    [DllImport("advapi32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    static extern uint StartTraceW(out ulong traceHandle, string instanceName, IntPtr properties);
    [DllImport("advapi32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    static extern uint ControlTraceW(ulong traceHandle, string instanceName, IntPtr properties, uint control);
    [DllImport("advapi32.dll", SetLastError = true)]
    static extern uint EnableTraceEx2(ulong traceHandle, ref Guid providerId, uint controlCode, byte level, ulong matchAny, ulong matchAll, uint timeout, IntPtr enableParams);
    [DllImport("advapi32.dll", SetLastError = true)]
    static extern ulong OpenTraceW(IntPtr logfile);
    [DllImport("advapi32.dll")]
    static extern uint ProcessTrace(ulong[] handles, uint count, IntPtr start, IntPtr end);
    [DllImport("advapi32.dll")]
    static extern uint CloseTrace(ulong handle);
    [DllImport("tdh.dll")]
    static extern uint TdhGetPropertySize(ref EVENT_RECORD rec, uint ctxCount, IntPtr ctx, uint propCount, ref PROPERTY_DATA_DESCRIPTOR desc, out uint size);
    [DllImport("tdh.dll")]
    static extern uint TdhGetProperty(ref EVENT_RECORD rec, uint ctxCount, IntPtr ctx, uint propCount, ref PROPERTY_DATA_DESCRIPTOR desc, uint bufSize, IntPtr buf);

    delegate void EventRecordCallback(ref EVENT_RECORD rec);
    static readonly EventRecordCallback _cb = OnEvent;   // 留引用防 GC

    [StructLayout(LayoutKind.Explicit)]
    struct EVENT_RECORD
    {
        [FieldOffset(0)] public ushort Size;
        [FieldOffset(12)] public uint ProcessId;
        [FieldOffset(24)] public Guid ProviderId;
        [FieldOffset(40)] public ushort Id;
        [FieldOffset(42)] public byte Version;
        [FieldOffset(44)] public byte Level;
        [FieldOffset(45)] public byte Opcode;
        [FieldOffset(48)] public long Keyword;
        [FieldOffset(84)] public ushort ExtendedDataCount;
        [FieldOffset(88)] public IntPtr ExtendedData;
        [FieldOffset(96)] public IntPtr UserData;
        [FieldOffset(104)] public IntPtr UserContext;
    }

    [StructLayout(LayoutKind.Sequential)]
    struct PROPERTY_DATA_DESCRIPTOR { public ulong PropertyName; public uint ArrayIndex; public uint Reserved; }

    static IntPtr _nPid, _nImg, _buf, _lfKeep, _nameKeep;

    static IntPtr BuildProps(string name)
    {
        byte[] nb = System.Text.Encoding.Unicode.GetBytes(name + "\0");
        int total = 2048;   // 胖缓冲：ControlTrace STOP/QUERY 会把会话统计+路径回写进来，小缓冲报 ERROR_BAD_LENGTH(24)
        IntPtr p = Marshal.AllocHGlobal(total);
        for (int i = 0; i < total; i++) Marshal.WriteByte(p, i, 0);
        Marshal.WriteInt32(p, 0, total);        // Wnode.BufferSize
        Marshal.WriteInt32(p, 40, 1);           // Wnode.ClientContext = QPC
        Marshal.WriteInt32(p, 44, 0x20000);     // Wnode.Flags = WNODE_FLAG_TRACED_GUID
        Marshal.WriteInt32(p, 48, 64);          // 每缓冲 64KB
        Marshal.WriteInt32(p, 52, 4);           // MinimumBuffers
        Marshal.WriteInt32(p, 56, 24);          // MaximumBuffers
        Marshal.WriteInt32(p, 64, 0x100);       // EVENT_TRACE_REAL_TIME_MODE
        Marshal.WriteInt32(p, 68, 1);           // FlushTimer=1s
        Marshal.WriteInt32(p, 116, 120);        // LoggerNameOffset
        Marshal.Copy(nb, 0, new IntPtr(p.ToInt64() + 120), nb.Length);
        return p;
    }

    /* ---------------- 诊断 -etwraw：Main 第一行的 StartTrace 裸测（排除初始化副作用） ---------------- */
    public static string RawProbe()
    {
        IntPtr props = BuildProps("ZkRawProbe");
        ulong h;
        uint rc = StartTraceW(out h, "ZkRawProbe", props);
        int gle = Marshal.GetLastWin32Error();
        return "StartTrace(ZkRawProbe) rc=" + rc + " gle=" + gle + " pid=" + System.Diagnostics.Process.GetCurrentProcess().Id;
    }

    public static bool Start()
    {
        lock (_sync)
        {
            if (_running) return true;
            Error = "";
            // 10-22：实时 ETW 会话要求 SeSystemProfilePrivilege 处于**启用**态——持有不算，必须 AdjustTokenPrivileges。
            // 默认禁用该特权的收紧系统上，ETW 启动前必须显式启用。
            // StartTrace 恒返 5（ACCESS_DENIED）：进程事件监听整个挂掉，帧率规则触发不了、进程列表永远"未运行"。
            SuiteApp.EnablePrivilege("SeSystemProfilePrivilege");
            if (_nPid == IntPtr.Zero)
            {
                _nPid = Marshal.StringToHGlobalUni("ProcessID");
                _nImg = Marshal.StringToHGlobalUni("ImageName");
                _buf = Marshal.AllocHGlobal(2048);
            }
            // 僵尸会话对抗：taskkill /F/崩溃会泄漏内核会话，同名 StartTrace 报 24/183。
            // 预清理+递增等待重试 3 次（内核回收有延迟；胖缓冲保证 ControlTrace STOP 回写成功）
            uint rc = 0;
            for (int attempt = 0; attempt < 3; attempt++)
            {
                IntPtr cp = BuildProps(SessionName);
                try { ControlTraceW(0, SessionName, cp, 1); } finally { Marshal.FreeHGlobal(cp); }   // 1=STOP（0 是查询）
                if (attempt > 0) Thread.Sleep(400 * attempt);
                IntPtr props = BuildProps(SessionName);
                try { rc = StartTraceW(out _session, SessionName, props); }
                finally { Marshal.FreeHGlobal(props); }
                if (rc == 0) break;
            }
            if (rc != 0)
            {
                Error = rc == 5 ? "StartTrace:5（需要管理员权限：SeSystemProfilePrivilege 不可用）" : "StartTrace:" + rc;
                return false;
            }

            Guid g = KernelProcess;
            uint rc2 = EnableTraceEx2(_session, ref g, 1, 4, 0x10, 0, 0, IntPtr.Zero);
            if (rc2 != 0) { Error = "EnableTraceEx2:" + rc2; StopSession(); return false; }

            _lfKeep = Marshal.AllocHGlobal(512);   // 结构体常驻不释放（内核回调引用）
            _nameKeep = Marshal.StringToHGlobalUni(SessionName);
            for (int i = 0; i < 512; i++) Marshal.WriteByte(_lfKeep, i, 0);
            Marshal.WriteIntPtr(_lfKeep, 8, _nameKeep);                                      // LoggerName @8
            Marshal.WriteInt32(_lfKeep, 28, 0x100 | 0x10000000);                             // ProcessTraceMode @28：REAL_TIME|EVENT_RECORD
            Marshal.WriteIntPtr(_lfKeep, 424, Marshal.GetFunctionPointerForDelegate(_cb));   // EventRecordCallback @424
            _trace = OpenTraceW(_lfKeep);
            if (_trace == 0 || _trace == ulong.MaxValue) { Error = "OpenTrace:" + Marshal.GetLastWin32Error(); StopSession(); return false; }

            _stop = false;
            _thread = new Thread(() => { var arr = new[] { _trace }; ProcessTrace(arr, 1, IntPtr.Zero, IntPtr.Zero); });
            _thread.IsBackground = true;
            _thread.Start();
            _running = true;
            return true;
        }
    }

    static void StopSession()
    {
        if (_session != 0)
        {
            IntPtr props = BuildProps(SessionName);
            try { ControlTraceW(_session, null, props, 1); } finally { Marshal.FreeHGlobal(props); }
            _session = 0;
        }
    }

    public static void Stop()
    {
        lock (_sync)
        {
            _stop = true;
            if (_trace != 0) { CloseTrace(_trace); _trace = 0; }   // ProcessTrace 线程随之返回
            StopSession();
            _running = false;
        }
    }

    // 引用计数共享：Iso 与 FirstCore 可同时持有会话，最后一个 Release 才真正停
    static int _refs;

    public static bool Acquire()
    {
        lock (_sync)
        {
            if (!Start()) return false;
            _refs++;
            return true;
        }
    }

    public static void Release()
    {
        lock (_sync)
        {
            if (_refs > 0) _refs--;
            if (_refs == 0) Stop();
        }
    }

    public static void ForceStop()   // 进程退出用：无视计数直接停
    {
        lock (_sync) _refs = 0;
        Stop();
    }

    static void OnEvent(ref EVENT_RECORD rec)
    {
        try
        {
            if (_stop) return;
            byte op = rec.Opcode;
            if (op == 1 || op == 3)          // start / rundown-start
            {
                int pid = GetPid(ref rec);
                string name = GetName(ref rec);
                if (pid > 0) { var h = Started; if (h != null) h(pid, name); }
            }
            else if (op == 2 || op == 4)     // stop / rundown-stop
            {
                int pid = GetPid(ref rec);
                if (pid > 0) { var h = Stopped; if (h != null) h(pid); }
            }
        }
        catch { }
    }

    static int GetPid(ref EVENT_RECORD rec)
    {
        var d = new PROPERTY_DATA_DESCRIPTOR { PropertyName = (ulong)_nPid.ToInt64(), ArrayIndex = 0xFFFFFFFF };
        uint size;
        if (TdhGetPropertySize(ref rec, 0, IntPtr.Zero, 1, ref d, out size) != 0 || size < 4) return -1;
        if (TdhGetProperty(ref rec, 0, IntPtr.Zero, 1, ref d, size, _buf) != 0) return -1;
        return Marshal.ReadInt32(_buf);
    }

    static string GetName(ref EVENT_RECORD rec)
    {
        var d = new PROPERTY_DATA_DESCRIPTOR { PropertyName = (ulong)_nImg.ToInt64(), ArrayIndex = 0xFFFFFFFF };
        uint size;
        if (TdhGetPropertySize(ref rec, 0, IntPtr.Zero, 1, ref d, out size) != 0 || size < 2) return "";
        if (TdhGetProperty(ref rec, 0, IntPtr.Zero, 1, ref d, size, _buf) != 0) return "";
        return Marshal.PtrToStringUni(_buf, (int)(size / 2) - 1);
    }
}

// ================= 核心隔离（游戏钉前台区，其余进程收拢隔离区；ETW 事件驱动零轮询） =================
// 两模式（09-11 用户定稿）：硬隔离=SetProcessAffinityMask 硬钉（前台区=隔离区补集，互斥）；
//   软隔离=SetProcessDefaultCpuSets 软引导（两区独立选核可重叠，负载高时可溢出，更温和）。
// 前台规则进程出现在 ETW start 事件 → 生效：前台→前台区，其余全部普通进程→隔离区（快照原值）。
// 后台规则独立生效：只钉指定进程进隔离区，不触发全局收拢。
// 最后一个前台实例退出 → 还原全局收拢；后台规则取消 → 单独还原（只还原仍等于钉入值的进程）。
// 开销：无规则=ETW 不起零成本；有规则=一条阻塞在 ProcessTrace 的线程（事件才醒）；
// 生效期每个新进程一次 OpenProcess+写落区（微秒级）。
// 已知限制：反作弊锁句柄的游戏（Vanguard 等）游戏本体钉核会 Access Denied——收拢照常，状态行如实提示。
static class Iso
{
    public static bool Engaged;
    public static string Status = "";
    public static event Action<string> StatusChanged;

    static readonly object _sync = new object();
    static readonly Dictionary<int, string> _games = new Dictionary<int, string>();   // 生效中的前台实例 pid→name
    static readonly Dictionary<int, Snap> _pinned = new Dictionary<int, Snap>();      // 全局收拢进程快照
    static readonly Dictionary<int, Snap> _backgroundPins = new Dictionary<int, Snap>();   // 独立后台规则快照
    static int _failCount;
    static string _firstGameName = "";
    static bool _watching, _shutdown;

    // 事件链排障日志（只记隔离关键事件，不记进程噪音；%TEMP%\dunsuitelite_isodbg.txt）
    public static void Dbg(string s)
    {
        try { File.AppendAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_isodbg.txt"), DateTime.Now.ToString("HH:mm:ss.fff ") + s + "\r\n"); } catch { }
    }

    class Snap { public UIntPtr Mask; public DateTime StartTime; public ulong Pinned; public bool Soft; public string Name; }   // Pinned=钉入时掩码；Name 供后台规则单独还原

    // 收拢豁免名单：系统关键进程（亲和本身无害，但这几个不值得动）+ 自身
    static readonly HashSet<string> _skip = new HashSet<string>(StringComparer.OrdinalIgnoreCase)
    {
        "system", "registry", "secure system", "memory compression", "idle",
        "smss", "csrss", "wininit", "winlogon", "services", "lsass", "lsaiso", "dunsuitelite"
    };

    public static void Init()
    {
        Topo.Detect();
        EnsureSoftDefaults();   // 软隔离空掩码默认全勾（修 09-11 空掩码永不生效坑；老配置自愈）
        FirstCore.DetectCpuSetApi();   // 软隔离需要 Set ID 映射（幂等，首核模块也用同一份）
        if (Cfg.IsoSoft == 1 && !Native.ProcCpuSetsOk)
        {
            SetStatus("软隔离不可用：系统缺少进程 CPU Sets API（需 Win10 1709+）");
            return;
        }
        RecoverOrphans();   // 上次异常死亡（taskkill /F/崩溃）的收拢残留还原——与规则无关，必须先跑
        lock (_sync)
        {
            if (Cfg.IsoRuleCount() > 0 && EnsureWatching())
            {
                UpdateStatus();
                StockCheckRules();   // 存量补查：前台触发全局隔离，后台独立落区
            }
            if (!Engaged) RepairStalePins();   // 非生效态发现恰好=隔离掩码的进程=历史尸体钉，后台受管进程除外
        }
    }

    static void StockCheckRules()
    {
        foreach (var rule in SnapshotRules())
        {
            Process[] procs;
            try { procs = Process.GetProcessesByName(rule.Key); } catch { continue; }
            foreach (var p in procs)
            {
                try
                {
                    if (rule.Value == 1)
                    {
                        if (!Engaged) Engage(rule.Key);
                        TrackGame(p.Id, rule.Key);
                    }
                    else TrackBackground(p, rule.Key);
                }
                catch { }
                p.Dispose();
            }
        }
    }

    // 尸体钉修复：亲和恰好=隔离掩码的进程只可能是我们（或旧版）钉入后没还原的——重置回全核心。
    // 软隔离同理：默认 CPU Set 恰好=软隔离区的进程清空集合。时机：启动时（非生效态）+ 每次解除隔离后。事件驱动，非轮询。
    static void RepairStalePins()
    {
        try
        {
            ulong iso, game;
            Zones(out iso, out game);
            if (iso == 0) return;
            bool soft = Cfg.IsoSoft == 1;
            if (soft && (FirstCore.CpuSetIds == null || !Native.ProcCpuSetsOk)) return;   // 无映射/无 API：判不了软钉，不碰
            SuiteApp.EnablePrivilege("SeDebugPrivilege");
            int self = Process.GetCurrentProcess().Id;
            int n = 0;
            foreach (var p in Process.GetProcesses())
            {
                try
                {
                    if (p.Id == self || p.Id == 0 || p.Id == 4 || _backgroundPins.ContainsKey(p.Id)) continue;
                    IntPtr h = Native.OpenProcess(0x200 | 0x1000 | 0x400, false, p.Id);
                    if (h == IntPtr.Zero) continue;
                    try
                    {
                        if (soft)
                        {
                            if (ReadProcSetsMask(h) == iso) { ClearProcSets(h); n++; }
                        }
                        else
                        {
                            UIntPtr cur, sys;
                            if (Native.GetProcessAffinityMask(h, out cur, out sys) && cur == (UIntPtr)iso)
                            { Native.SetProcessAffinityMask(h, (UIntPtr)Topo.AllMask); n++; }
                        }
                    }
                    finally { Native.CloseHandle(h); }
                }
                catch { }
                finally { p.Dispose(); }
            }
            if (n > 0) Dbg("stale pin repair: " + n + " 个还原");
        }
        catch { }
    }

    public static void Shutdown()
    {
        EtwProc.ForceStop();   // 进程退出：无视 FirstCore 引用直接停（它随 ExitApp 随后自行还原，不依赖事件）
        lock (_sync)
        {
            _shutdown = true;
            if (Engaged) Disengage();
            RestoreBackground(null);
        }
    }

    static bool EnsureWatching()
    {
        if (_watching) return true;
        if (!Topo.Supported) { SetStatus("核心拓扑检测失败（或 >64 逻辑处理器），隔离不可用"); Dbg("EnsureWatching: topo unsupported"); return false; }
        if (!EtwProc.Acquire())
        {
            SetStatus("进程事件监听启动失败：" + EtwProc.Error + "（将自动重试）");
            Dbg("EnsureWatching: EtwProc.Start FAIL " + EtwProc.Error);
            ScheduleWatchRetry();   // 僵尸会话内核回收有延迟：一次性定时器重连（非轮询）
            return false;
        }
        EtwProc.Started += OnProcStart;   // 成功后才挂订阅：防失败重试叠加
        EtwProc.Stopped += OnProcStop;
        _watching = true;
        _watchRetry = 0;
        Dbg("EnsureWatching: ETW up");
        return true;
    }

    static int _watchRetry;
    static readonly int[] _watchRetryDelays = { 5000, 10000, 30000, 60000, 120000 };

    static void ScheduleWatchRetry()
    {
        if (_watchRetry >= _watchRetryDelays.Length) return;
        int delay = _watchRetryDelays[_watchRetry];
        _watchRetry++;
        Dbg("watch retry #" + _watchRetry + " in " + delay + "ms");
        ScheduleOnce(delay, () =>
        {
            lock (_sync)
            {
                if (_watching || _shutdown) return;
                if (Cfg.IsoRuleCount() == 0) return;
                if (EnsureWatching()) StockCheckRules();   // 监听恢复后补查两类规则
            }
        });
    }

    // 一次性延时执行（非轮询：单次触发即销毁）
    static void ScheduleOnce(int ms, Action a)
    {
        System.Threading.Timer t = null;
        t = new System.Threading.Timer(_ => { try { a(); } catch { } try { t.Dispose(); } catch { } }, null, ms, Timeout.Infinite);
    }

    static void StopWatching()   // 调用方不得持有 _sync（CloseTrace 会等 ETW 线程退出回调）
    {
        if (!_watching) return;
        _watching = false;
        EtwProc.Release();   // FirstCore 可能还持有会话：引用计数，最后一个释放才真停
    }

    /* ---- ETW 事件（ProcessTrace 线程） ---- */
    static void OnProcStart(int pid, string imagePath)
    {
        string name = FileName(imagePath);
        if (name.Length == 0) return;
        int mode = Cfg.IsoRuleMode(name);
        lock (_sync)
        {
            if (_shutdown) return;
            if (mode == 1)
            {
                Dbg("game start: " + name + " pid=" + pid + " engaged=" + Engaged);
                if (Engaged)
                {
                    // 自愈：stop 事件漏收导致 Engaged 残留（登记的游戏全死）→ 先还原再重新生效
                    var dead = new List<int>();
                    foreach (var gpid in _games.Keys) if (!PidAlive(gpid)) dead.Add(gpid);
                    foreach (var gpid in dead) _games.Remove(gpid);
                    if (_games.Count == 0) { Dbg("stale engaged healed (stop event missed)"); Disengage(); }
                }
                if (!Engaged) Engage(name);
                TrackGame(pid, name);
            }
            else if (mode == 2)
            {
                using (var p = Process.GetProcessById(pid)) TrackBackground(p, name);
            }
            else if (Engaged)
            {
                PinOne(pid, name);   // 生效期新进程：收拢
                VerifyGamePins("进程启动");   // 顺带校验游戏钉（事件免费通道，3s 去抖）
            }
        }
    }

    static void OnProcStop(int pid)
    {
        lock (_sync)
        {
            if (_shutdown || !Engaged || !_games.ContainsKey(pid)) return;
            Dbg("game stop: pid=" + pid + " left=" + (_games.Count - 1));
            _games.Remove(pid);
            if (_games.Count == 0) Disengage();
            else UpdateStatus();
        }
    }

    /* ---- UI 入口（UI 线程） ---- */
    public static void RuleChanged(string name, int oldMode, int mode)
    {
        bool stopWatch = false;
        lock (_sync)
        {
            if (oldMode == 1 && mode != 1 && Engaged)
            {
                var gone = new List<int>();
                foreach (var kv in _games) if (string.Equals(kv.Value, name, StringComparison.OrdinalIgnoreCase)) gone.Add(kv.Key);
                foreach (var pid in gone) _games.Remove(pid);
                if (_games.Count == 0) Disengage(); else UpdateStatus();
            }
            if (oldMode == 2 && mode != 2) RestoreBackground(name);
            if (mode == 0 && Engaged)
            {
                ulong iso, game;
                Zones(out iso, out game);
                try { foreach (var p in Process.GetProcessesByName(name)) { PinOne(p, name, iso, null); p.Dispose(); } }
                catch { }
            }
            if (mode != 0)
            {
                if (!EnsureWatching()) return;
                bool any = false;
                try
                {
                    foreach (var p in Process.GetProcessesByName(name))
                    {
                        if (mode == 1)
                        {
                            if (!Engaged) Engage(name);
                            TrackGame(p.Id, name);
                        }
                        else TrackBackground(p, name);
                        any = true;
                        p.Dispose();
                    }
                }
                catch { }
                if (!any) UpdateStatus();
            }
            stopWatch = Cfg.IsoRuleCount() == 0 && !Engaged && _backgroundPins.Count == 0;
        }
        if (stopWatch)
        {
            StopWatching();
            try { File.Delete(FlagFile); } catch { }
            SetStatus("");
        }
    }

    public static void MaskChanged()
    {
        lock (_sync)
        {
            RestoreBackground(null);
            if (Engaged) Disengage();
            StockCheckRules();
            UpdateStatus();
        }
    }

    /* ---- 引擎 ---- */
    // 当前模式两区：硬隔离=前台区是隔离区补集；软隔离=两区独立掩码（可重叠）；UI/首核/中断联动共用
    public static void Zones(out ulong iso, out ulong game)
    {
        if (Cfg.IsoSoft == 1)
        {
            iso = Cfg.SoftIsoMask & Topo.AllMask;
            game = Cfg.SoftGameMask & Topo.AllMask;
        }
        else
        {
            iso = Cfg.IsoMask & Topo.AllMask;
            game = Topo.AllMask & ~iso;
        }
    }

    static bool MaskValid(out ulong iso, out ulong game)
    {
        Zones(out iso, out game);
        return iso != 0 && game != 0;
    }

    // 软隔离空掩码默认全勾（两区独立可重叠，全勾=无引导，用户按需取消；修 09-11"首次设置不勾选永不生效"坑）
    // 返回 true=发生了默认填充（调用方据此跳过中断联动——默认全勾非用户选核意图，中断落点保持原样等实际调区）
    public static bool EnsureSoftDefaults()
    {
        if (Cfg.IsoSoft != 1 || Topo.AllMask == 0) return false;
        bool chg = false;
        if ((Cfg.SoftGameMask & Topo.AllMask) == 0)
        {
            Cfg.SoftGameMask = Topo.AllMask;
            Cfg.SaveKey("ISO_SOFT_GAME", Topo.AllMask.ToString("X"));
            chg = true;
        }
        if ((Cfg.SoftIsoMask & Topo.AllMask) == 0)
        {
            Cfg.SoftIsoMask = Topo.AllMask;
            Cfg.SaveKey("ISO_SOFT_ISO", Topo.AllMask.ToString("X"));
            chg = true;
        }
        return chg;
    }

    /* ---- 软隔离：进程级 CPU Sets（默认集=软引导，负载可溢出；映射复用首核 FirstCore.CpuSetIds） ---- */
    static uint[] MaskToSetIds(ulong mask)
    {
        var map = FirstCore.CpuSetIds;
        if (map == null) return null;
        var ids = new List<uint>();
        for (int i = 0; i < map.Length; i++) if ((mask & (1UL << i)) != 0) ids.Add(map[i]);
        return ids.ToArray();
    }

    static bool SetProcSets(IntPtr h, ulong mask)
    {
        uint[] ids = MaskToSetIds(mask);
        if (ids == null || ids.Length == 0) return false;
        IntPtr buf = Marshal.AllocHGlobal(ids.Length * 4);
        try
        {
            for (int i = 0; i < ids.Length; i++) Marshal.WriteInt32(buf, i * 4, (int)ids[i]);
            return Native.SetProcessDefaultCpuSets(h, buf, (uint)ids.Length);
        }
        finally { Marshal.FreeHGlobal(buf); }
    }

    static bool ClearProcSets(IntPtr h)   // 清空默认集=恢复无约束（原进程无集时的还原路径）
    {
        return Native.SetProcessDefaultCpuSets(h, IntPtr.Zero, 0);
    }

    // 读进程默认 CPU Set→掩码；无集/读失败=0（快照 orig=0 表示原本无集）
    // 协议坑（09-11 实测）：有默认集时首次 NULL 询问返回 FALSE+122(缓冲不足)+req=真实大小；无集返回 TRUE+req=0
    static ulong ReadProcSetsMask(IntPtr h)
    {
        uint req;
        if (!Native.GetProcessDefaultCpuSets(h, IntPtr.Zero, 0, out req))
        {
            if (Marshal.GetLastWin32Error() != 122) return 0;   // 122=缓冲不足（正常协议，req 已填）；其他错误=无默认集
        }
        if (req == 0) return 0;
        IntPtr buf = Marshal.AllocHGlobal((int)(req * 4));
        try
        {
            if (!Native.GetProcessDefaultCpuSets(h, buf, req, out req)) return 0;
            var map = FirstCore.CpuSetIds;
            if (map == null) return 0;
            ulong m = 0;
            for (uint i = 0; i < req; i++)
            {
                uint id = (uint)Marshal.ReadInt32(buf, (int)(i * 4));
                for (int j = 0; j < map.Length; j++) if (map[j] == id) m |= 1UL << j;
            }
            return m;
        }
        finally { Marshal.FreeHGlobal(buf); }
    }

    // 当前落区读/写：硬隔离=进程亲和掩码，软隔离=默认 CPU Set（无=0）
    static ulong ReadZone(IntPtr h)
    {
        if (Cfg.IsoSoft == 1) return ReadProcSetsMask(h);
        UIntPtr cur, sys;
        if (!Native.GetProcessAffinityMask(h, out cur, out sys)) return 0;
        return cur.ToUInt64();
    }

    static bool WriteZone(IntPtr h, ulong mask)
    {
        if (Cfg.IsoSoft == 1) return SetProcSets(h, mask);
        return Native.SetProcessAffinityMask(h, (UIntPtr)mask);
    }

    static void Engage(string gameName)
    {
        ulong iso, gameMask;
        if (!MaskValid(out iso, out gameMask)) { SetStatus("隔离区未勾选核心（或全选无效），无法生效"); return; }
        if (Cfg.IsoSoft == 1 && (FirstCore.CpuSetIds == null || !Native.ProcCpuSetsOk))
        { SetStatus("软隔离不可用：系统缺少进程 CPU Sets API（需 Win10 1709+）"); return; }
        SuiteApp.EnablePrivilege("SeDebugPrivilege");
        Engaged = true;
        _firstGameName = gameName;
        _failCount = 0;
        _pinned.Clear();
        int self = Process.GetCurrentProcess().Id;
        var fsb = new System.Text.StringBuilder();
        foreach (var p in Process.GetProcesses())
        {
            try
            {
                if (p.Id == self || p.Id == 0 || p.Id == 4) continue;
                string n;
                try { n = p.ProcessName; } catch { continue; }
                if (_skip.Contains(n) || IsGameName(n) || IsBackgroundName(n) || IsOptimizationTargetName(n)) continue;
                PinOne(p, n, iso, fsb);
            }
            catch { }
            finally { p.Dispose(); }
        }
        try { File.WriteAllText(FlagFile, fsb.ToString()); } catch { }
        RewriteFlagFile();   // 全局与独立后台快照共用一份崩溃恢复文件
        Dbg("Engage done: pinned=" + _pinned.Count + " fail=" + _failCount);
        UpdateStatus();
    }

    static void TrackGame(int pid, string name)
    {
        _games[pid] = name;
        ulong iso, gameMask;
        if (!MaskValid(out iso, out gameMask)) return;
        IntPtr h = Native.OpenProcess(0x200 | 0x1000 | 0x400, false, pid);   // SET_INFORMATION | QUERY_LIMITED | SET_LIMITED（软隔离 CPU Sets 需 0x400）
        if (h == IntPtr.Zero) { SetStatus(name + ".exe 受保护无法钉核（反作弊？），其余进程已收拢"); Dbg("TrackGame " + name + " pid=" + pid + " OpenProcess FAIL " + Marshal.GetLastWin32Error()); return; }
        try
        {
            if (!WriteZone(h, gameMask))
            {
                SetStatus(name + ".exe 钉核失败(err " + Marshal.GetLastWin32Error() + ")，其余进程已收拢");
                Dbg("TrackGame " + name + " pid=" + pid + " WriteZone FAIL " + Marshal.GetLastWin32Error());
            }
            else
            {
                Dbg("TrackGame " + name + " pid=" + pid + " pinned to game zone OK");
                UpdateStatus();
                // 防游戏自复位：部分游戏/反作弊启动初期会自己重置亲和，+8s/+20s 各补钉一次（一次性定时器，非轮询）
                ScheduleRepin(pid, name);
            }
        }
        finally { Native.CloseHandle(h); }
    }

    static void ScheduleRepin(int pid, string name)
    {
        // 受反作弊保护的游戏实测：游戏/反作弊会多次自复位亲和，开机自启等慢环境复位可拖到 1 分钟后
        ScheduleOnce(8000, () => Repin(pid, name));
        ScheduleOnce(20000, () => Repin(pid, name));
        ScheduleOnce(40000, () => Repin(pid, name));
        ScheduleOnce(90000, () => Repin(pid, name));
    }

    static DateTime _lastVerify;

    // 校验所有在登记游戏的亲和，漂移则补钉。调用方须持有 _sync。3s 去抖防事件风暴。
    static void VerifyGamePins(string why)
    {
        if (!Engaged || _games.Count == 0) return;
        if ((DateTime.Now - _lastVerify).TotalSeconds < 3) return;
        _lastVerify = DateTime.Now;
        ulong iso, game;
        if (!MaskValid(out iso, out game)) return;
        foreach (var kv in new List<KeyValuePair<int, string>>(_games))
        {
            IntPtr h = Native.OpenProcess(0x200 | 0x1000 | 0x400, false, kv.Key);
            if (h == IntPtr.Zero) continue;
            try
            {
                ulong cur = ReadZone(h);
                if (cur != game && WriteZone(h, game))
                    Dbg("Verify(" + why + "): " + kv.Value + " pid=" + kv.Key + " 漂移已纠正 was=0x" + cur.ToString("X"));
            }
            finally { Native.CloseHandle(h); }
        }
    }

    // 窗口激活顺带校验（Shell Hook 已有事件，零新增开销）
    public static void OnWindowActive()
    {
        if (!Engaged) return;
        lock (_sync) { VerifyGamePins("窗口激活"); }
    }

    static void Repin(int pid, string name)
    {
        lock (_sync)
        {
            if (_shutdown || !Engaged || !_games.ContainsKey(pid)) return;
            ulong iso, game;
            if (!MaskValid(out iso, out game)) return;
            IntPtr h = Native.OpenProcess(0x200 | 0x1000 | 0x400, false, pid);
            if (h == IntPtr.Zero) return;
            try
            {
                ulong cur = ReadZone(h);
                if (cur != game && WriteZone(h, game))
                    Dbg("Repin " + name + " pid=" + pid + "（游戏自复位已纠正）");
            }
            finally { Native.CloseHandle(h); }
        }
    }

    static bool PidAlive(int pid)
    {
        IntPtr h = Native.OpenProcess(0x1000, false, pid);   // QUERY_LIMITED
        if (h == IntPtr.Zero) return false;
        Native.CloseHandle(h);
        return true;
    }

    static void PinOne(int pid, string name)
    {
        if (_skip.Contains(name) || IsGameName(name) || IsBackgroundName(name) || IsOptimizationTargetName(name)) return;
        try
        {
            ulong iso, game;
            Zones(out iso, out game);
            using (var p = Process.GetProcessById(pid))
                PinOne(p, name, iso, null);
        }
        catch { }   // 进程已退出
    }

    static void TrackBackground(Process p, string name)
    {
        if (_skip.Contains(name)) return;
        ulong iso, game;
        if (!MaskValid(out iso, out game)) { SetStatus("隔离区未勾选核心（或全选无效），后台规则无法生效"); return; }
        PinOne(p, name, iso, null, _backgroundPins);
        UpdateStatus();
    }

    static void RestoreBackground(string name)
    {
        foreach (var kv in new List<KeyValuePair<int, Snap>>(_backgroundPins))
        {
            if (name != null && !string.Equals(kv.Value.Name, name, StringComparison.OrdinalIgnoreCase)) continue;
            IntPtr h = Native.OpenProcess(0x200 | 0x1000 | 0x400, false, kv.Key);
            if (h != IntPtr.Zero)
            {
                try
                {
                    bool same = true;
                    if (kv.Value.StartTime != DateTime.MinValue)
                    {
                        try { using (var p = Process.GetProcessById(kv.Key)) same = p.StartTime == kv.Value.StartTime; }
                        catch { same = false; }
                    }
                    if (same)
                    {
                        if (kv.Value.Soft)
                        {
                            if (ReadProcSetsMask(h) == kv.Value.Pinned)
                            {
                                ulong orig = kv.Value.Mask.ToUInt64();
                                if (orig == 0) ClearProcSets(h); else SetProcSets(h, orig);
                            }
                        }
                        else
                        {
                            UIntPtr cur, sys;
                            if (Native.GetProcessAffinityMask(h, out cur, out sys) && cur == (UIntPtr)kv.Value.Pinned)
                                Native.SetProcessAffinityMask(h, kv.Value.Mask);
                        }
                    }
                }
                finally { Native.CloseHandle(h); }
            }
            _backgroundPins.Remove(kv.Key);
        }
        RewriteFlagFile();
        UpdateStatus();
    }

    static void PinOne(Process p, string name, ulong iso, System.Text.StringBuilder fsb, Dictionary<int, Snap> target = null)
    {
        var pins = target ?? _pinned;
        bool soft = Cfg.IsoSoft == 1;
        IntPtr h = Native.OpenProcess(0x200 | 0x1000 | 0x400, false, p.Id);
        if (h == IntPtr.Zero) { _failCount++; return; }
        try
        {
            DateTime st;
            try { st = p.StartTime; } catch { st = DateTime.MinValue; }
            if (soft)
            {
                ulong cur = ReadProcSetsMask(h);
                if (cur == iso) return;   // 已在隔离区（或第三方早已如此设置）：不碰不跟踪
                if (SetProcSets(h, iso))
                {
                    pins[p.Id] = new Snap { Mask = (UIntPtr)cur, StartTime = st, Pinned = iso, Soft = true, Name = name };
                    string line = p.Id + "|" + st.Ticks + "|" + cur.ToString("X") + "|" + iso.ToString("X") + "|S\r\n";
                    if (fsb != null) fsb.Append(line);
                    else FlagAppend(line);
                }
                else _failCount++;
                return;
            }
            UIntPtr curA, sys;
            if (!Native.GetProcessAffinityMask(h, out curA, out sys)) { _failCount++; return; }
            if (curA == (UIntPtr)iso) return;   // 已在隔离区（或第三方早已如此设置）：不碰不跟踪
            if (Native.SetProcessAffinityMask(h, (UIntPtr)iso))
            {
                pins[p.Id] = new Snap { Mask = curA, StartTime = st, Pinned = iso, Name = name };
                string line = p.Id + "|" + st.Ticks + "|" + curA.ToUInt64().ToString("X") + "|" + iso.ToString("X") + "|H\r\n";
                if (fsb != null) fsb.Append(line);
                else FlagAppend(line);
            }
            else _failCount++;
        }
        finally { Native.CloseHandle(h); }
    }

    static string FlagFile { get { return Path.Combine(Cfg.Dir, "iso_pinned.dat"); } }

    static void FlagAppend(string line)
    {
        try { File.AppendAllText(FlagFile, line); } catch { }
    }

    static void RewriteFlagFile()
    {
        try
        {
            if (_pinned.Count == 0 && _backgroundPins.Count == 0) { File.Delete(FlagFile); return; }
            var sb = new System.Text.StringBuilder();
            foreach (var pins in new[] { _pinned, _backgroundPins })
                foreach (var kv in pins)
                    sb.Append(kv.Key + "|" + kv.Value.StartTime.Ticks + "|" + kv.Value.Mask.ToUInt64().ToString("X")
                        + "|" + kv.Value.Pinned.ToString("X") + "|" + (kv.Value.Soft ? "S" : "H") + "\r\n");
            File.WriteAllText(FlagFile, sb.ToString());
        }
        catch { }
    }

    // 启动时还原上次异常死亡的收拢残留（PID+StartTime 校验防复用，只还原仍等于钉入值的）
    static void RecoverOrphans()
    {
        try
        {
            if (!File.Exists(FlagFile)) return;
            ulong iso, game;
            Zones(out iso, out game);
            if (iso == 0) { File.Delete(FlagFile); return; }
            int restored = 0;
            foreach (var line in File.ReadAllLines(FlagFile))
            {
                var parts = line.Split('|');
                if (parts.Length < 3) continue;
                int pid; long ticks; ulong orig;
                if (!int.TryParse(parts[0], out pid)) continue;
                if (!long.TryParse(parts[1], out ticks)) continue;
                if (!ulong.TryParse(parts[2], System.Globalization.NumberStyles.HexNumber, null, out orig)) continue;
                ulong pinnedWith = iso;   // 第 4 段=钉入时掩码（旧 3 段格式回退用当前掩码）
                if (parts.Length >= 4) ulong.TryParse(parts[3], System.Globalization.NumberStyles.HexNumber, null, out pinnedWith);
                bool soft = parts.Length >= 5 && parts[4] == "S";   // 第 5 段=钉入模式（旧 4 段无此段→硬）
                if (pinnedWith == 0) continue;
                if (soft && (FirstCore.CpuSetIds == null || !Native.ProcCpuSetsOk)) continue;   // 软残留但 API 不可用：还原不了，不碰
                IntPtr h = Native.OpenProcess(0x200 | 0x1000 | 0x400, false, pid);
                if (h == IntPtr.Zero) continue;
                try
                {
                    bool same;
                    try { using (var p = Process.GetProcessById(pid)) same = p.StartTime.Ticks == ticks; } catch { same = false; }
                    if (!same) continue;
                    if (soft)
                    {
                        if (ReadProcSetsMask(h) != pinnedWith) continue;
                        if (orig == 0) ClearProcSets(h); else SetProcSets(h, orig);
                        restored++;
                    }
                    else
                    {
                        UIntPtr cur, sys;
                        if (Native.GetProcessAffinityMask(h, out cur, out sys) && cur == (UIntPtr)pinnedWith)
                        {
                            Native.SetProcessAffinityMask(h, (UIntPtr)orig);
                            restored++;
                        }
                    }
                }
                finally { Native.CloseHandle(h); }
            }
            File.Delete(FlagFile);
            if (restored > 0) Dbg("crash recovery: restored " + restored + " orphan pins");
        }
        catch { }
    }

    static void Disengage()
    {
        foreach (var kv in _pinned)
        {
            IntPtr h = Native.OpenProcess(0x200 | 0x1000 | 0x400, false, kv.Key);
            if (h == IntPtr.Zero) continue;   // 已退出
            try
            {
                if (kv.Value.StartTime != DateTime.MinValue)   // PID 复用校验
                {
                    bool same;
                    try { using (var p = Process.GetProcessById(kv.Key)) same = p.StartTime == kv.Value.StartTime; }
                    catch { same = false; }
                    if (!same) continue;
                }
                if (kv.Value.Soft)
                {
                    if (ReadProcSetsMask(h) != kv.Value.Pinned) continue;   // 只还原仍等于钉入值的（第三方改过的尊重不动）
                    ulong orig = kv.Value.Mask.ToUInt64();
                    if (orig == 0) ClearProcSets(h); else SetProcSets(h, orig);
                }
                else
                {
                    UIntPtr cur, sys;
                    if (!Native.GetProcessAffinityMask(h, out cur, out sys)) continue;
                    if (cur == (UIntPtr)kv.Value.Pinned)   // 只还原仍等于钉入值的（第三方改过的尊重不动；按钉入时掩码判，掩码变更也不漏还原）
                        Native.SetProcessAffinityMask(h, kv.Value.Mask);
                }
            }
            finally { Native.CloseHandle(h); }
        }
        _pinned.Clear();
        _games.Clear();
        Engaged = false;
        RewriteFlagFile();   // 只作废全局快照，独立后台规则仍保留崩溃恢复信息
        RepairStalePins();   // 兜底：未跟踪的尸体钉（旧版/历史残留）一并还原
        Dbg("Disengage done");
        UpdateStatus();
    }

    /* ---- 工具 ---- */
    static bool IsGameName(string n)
    {
        lock (Cfg.IsoGames) return Cfg.IsoGames.Contains(n);
    }

    static bool IsBackgroundName(string n)
    {
        lock (Cfg.IsoBackgrounds) return Cfg.IsoBackgrounds.Contains(n);
    }

    static bool IsOptimizationTargetName(string n)
    {
        lock (Cfg.FcRules) if (Cfg.FcRules.ContainsKey(n)) return true;
        return false;
    }

    static List<KeyValuePair<string, int>> SnapshotRules()
    {
        var rules = new List<KeyValuePair<string, int>>();
        lock (Cfg.IsoGames) foreach (var n in Cfg.IsoGames) rules.Add(new KeyValuePair<string, int>(n, 1));
        lock (Cfg.IsoBackgrounds) foreach (var n in Cfg.IsoBackgrounds) rules.Add(new KeyValuePair<string, int>(n, 2));
        return rules;
    }

    static string FileName(string imagePath)
    {
        if (string.IsNullOrEmpty(imagePath)) return "";
        int i = imagePath.LastIndexOf('\\');
        string n = i >= 0 ? imagePath.Substring(i + 1) : imagePath;
        if (n.EndsWith(".exe", StringComparison.OrdinalIgnoreCase)) n = n.Substring(0, n.Length - 4);
        return n;
    }

    static void UpdateStatus()
    {
        if (!Engaged)
        {
            int rules = Cfg.IsoRuleCount();
            if (_backgroundPins.Count > 0) SetStatus("后台隔离中 · 已收拢 " + _backgroundPins.Count + " 个进程 · 共 " + rules + " 条核心规则");
            else SetStatus(rules > 0 ? "待命：" + rules + " 条核心规则，前台启动自动生效" : "");
            return;
        }
        string modeName = Cfg.IsoSoft == 1 ? "软隔离" : "硬隔离";
        SetStatus(string.Format(modeName + "生效中 · {0}.exe 在前台区 · 已收拢 {1} 个进程{2}",
            _firstGameName, _pinned.Count, _failCount > 0 ? "（" + _failCount + " 个受保护跳过）" : ""));
    }

    public static void SetStatus(string s)
    {
        Status = s;
        var h = StatusChanged; if (h != null) try { h(s); } catch { }
    }

    // 诊断 -isoengage <name>：强制生效→取证→还原（独立短进程，结束即还原不留痕；按当前配置模式演练）
    public static string TestEngage(string name)
    {
        Cfg.Load();
        Topo.Detect();
        EnsureSoftDefaults();   // 与实际启动路径一致：空掩码默认全勾后再校验
        FirstCore.DetectCpuSetApi();
        var sb = new System.Text.StringBuilder();
        ulong iso, game;
        MaskValid(out iso, out game);
        sb.AppendLine("topo: supported=" + Topo.Supported + " logical=" + Topo.LogicalCount
            + " mode=" + (Cfg.IsoSoft == 1 ? "soft" : "hard")
            + " iso=0x" + iso.ToString("X") + " game=0x" + game.ToString("X")
            + " cpuSetApi=" + (FirstCore.CpuSetIds != null) + " procCpuSets=" + Native.ProcCpuSetsOk);
        lock (_sync)
        {
            if (!MaskValid(out iso, out game)) { sb.AppendLine("FAIL: 隔离区配置无效（iso=0x" + iso.ToString("X") + " game=0x" + game.ToString("X") + "）"); return sb.ToString(); }
            lock (Cfg.IsoGames) Cfg.IsoGames.Add(name);

            string expBefore = ProbeZone("explorer");
            Engage(name);
            int gameInst = 0;
            try
            {
                foreach (var p in Process.GetProcessesByName(name)) { TrackGame(p.Id, name); gameInst++; p.Dispose(); }
            }
            catch { }
            string expDuring = ProbeZone("explorer");
            string gameDuring = gameInst > 0 ? ProbeZone(name) : "(未在跑)";
            sb.AppendLine("engaged: gameInst=" + gameInst + " pinned=" + _pinned.Count + " failed=" + _failCount);
            sb.AppendLine("explorer: before=" + expBefore + " during=" + expDuring + " (期望 during=0x" + iso.ToString("X") + ")");
            sb.AppendLine(name + ": during=" + gameDuring + " (期望=0x" + game.ToString("X") + ")");
            Disengage();
            sb.AppendLine("explorer: after=" + ProbeZone("explorer") + "（应还原为 before）");
            sb.AppendLine("status: " + Status);
            return sb.ToString();
        }
    }

    // 按模式取落区：软=默认 CPU Set 掩码，硬=进程亲和掩码
    static string ProbeZone(string procName)
    {
        if (Cfg.IsoSoft == 1)
        {
            try
            {
                var procs = Process.GetProcessesByName(procName);
                if (procs.Length == 0) return "(无此进程)";
                var p = procs[0];
                IntPtr h = Native.OpenProcess(0x1000 | 0x400, false, p.Id);
                string r = "?";
                if (h != IntPtr.Zero)
                {
                    ulong m = ReadProcSetsMask(h);
                    r = m == 0 ? "0x0(无默认集)" : "0x" + m.ToString("X");
                    Native.CloseHandle(h);
                }
                else r = "OpenFail:" + Marshal.GetLastWin32Error();
                foreach (var x in procs) x.Dispose();
                return r;
            }
            catch (Exception ex) { return "ex:" + ex.Message; }
        }
        return ProbeMask(procName);
    }

    static string ProbeMask(string procName)
    {
        try
        {
            var procs = Process.GetProcessesByName(procName);
            if (procs.Length == 0) return "(无此进程)";
            var p = procs[0];
            IntPtr h = Native.OpenProcess(0x1000, false, p.Id);
            UIntPtr cur, sys;
            string r = "?";
            if (h != IntPtr.Zero)
            {
                if (Native.GetProcessAffinityMask(h, out cur, out sys)) r = "0x" + cur.ToUInt64().ToString("X");
                else r = "GetFail:" + Marshal.GetLastWin32Error();
                Native.CloseHandle(h);
            }
            else r = "OpenFail:" + Marshal.GetLastWin32Error();
            foreach (var x in procs) x.Dispose();
            return r;
        }
        catch (Exception ex) { return "ex:" + ex.Message; }
    }
}

// ================= 首核调度（游戏主线程钉核：CPU Sets 精确钉单线程+Ideal 同值，恒硬） =================
// 首核=逻辑线程号（0..LogicalCount-1，选 5 就是第 6 个线程）；前台区限制只约束前台规则进程，其他进程全核可选。
// 规则独立：FC_<name>=4 持久化；ETW 进程启动事件驱动（与 Iso 引用计数共享会话），无规则零开销。
// 主线程识别：线程起始地址落在 exe 主模块范围内 + 取创建时间最早者交叉验证；认不出=零写拒绝，不乱钉。
// 强身份：PID+进程启动时间+TID+线程创建时间，每次读写前校验；对不上=不写入（D13 原则）。
// 节奏=启动即写 + 1/3/6/10/30 秒一次性补写；窗口激活时再校验与重梳理，无周期轮询。
//   补写意义：反作弊游戏常晚期才重建真主线程/自设亲和，阶段补写与激活事件共同接住；一次性定时器到点即毁。
// 梳理：写入主线程时顺手把 Ideal 落在首核整核 [N,N+1] 上的同进程其他线程挪到游戏空闲核
//   （池=前台区（隔离语义，未设隔离=全核）减首核整核；已有第三方 CPU Sets 的线程尊重不碰）。
// 还原语义=比较还原：当前值仍是我们写入的目标才还原快照，第三方接管则尊重不动。
// 已知边界：反作弊锁句柄的游戏 OpenProcess/OpenThread 直接失败→跳过并提示，绝不硬来。
static class FirstCore
{
    public static Action<string> Status;   // → SuiteApp.SliceMsg（托盘期也留痕）

    // 分阶段补写节奏（ms）：首写后算起，到点重仲裁+重写+重梳理；全部完成后永久放手
    static readonly int[] StageMs = { 1000, 3000, 6000, 10000, 30000 };

    class Swept   // 被梳理线程的还原快照
    {
        public uint Tid;
        public ulong Create;
        public Native.PROCESSOR_NUMBER Orig;
        public Native.PROCESSOR_NUMBER Target;
    }

    class Eng
    {
        public string Name;
        public DateTime ProcStart;              // UTC，进程身份
        public uint Tid;
        public ulong ThreadCreate;              // 100ns UTC，线程身份
        public int Core;                        // 物理核索引（Topo.Cores）
        public Native.PROCESSOR_NUMBER Ideal;   // 目标 Ideal=首核第一个逻辑 CPU
        public uint[] PairIds;                  // 硬模式：[setId(N), setId(N+1)]
        public uint[] OrigSets;                 // 接管前 CPU Sets（长度0=原本未设）
        public Native.PROCESSOR_NUMBER OrigIdeal;
        public readonly List<Swept> Swept = new List<Swept>();
    }

    static readonly object _sync = new object();
    static readonly Dictionary<int, Eng> _eng = new Dictionary<int, Eng>();
    static bool _watching, _shutdown, _subscribed, _seDebug;
    static uint[] _cpuSetIds;                   // 逻辑 CPU 序号 → CPU Set Id（仅组0）
    static bool _cpuSetApi;
    public static bool HardSupported { get { return _cpuSetApi; } }
    public static uint[] CpuSetIds { get { return _cpuSetIds; } }   // 算法一复用同一映射

    const uint TH_SET = 0x20, TH_QUERY = 0x40;
    const uint P_QLIMITED = 0x1000, P_VMREAD = 0x10;

    static void Msg(string m) { Dbg(m); var h = Status; if (h != null) h(m); }

    // 事件链排障日志（与 Iso 同款；%TEMP%\dunsuitelite_fcdbg.txt）——拒绝/生效不再无声
    public static void Dbg(string s)
    {
        try { File.AppendAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_fcdbg.txt"), DateTime.Now.ToString("HH:mm:ss.fff ") + s + "\r\n"); } catch { }
    }

    static bool PidAlive(int pid)
    {
        try { var p = Process.GetProcessById(pid); p.Dispose(); return true; }
        catch { return false; }
    }

    static string FileName(string imagePath)
    {
        if (string.IsNullOrEmpty(imagePath)) return "";
        int i = imagePath.LastIndexOf('\\');
        string n = i >= 0 ? imagePath.Substring(i + 1) : imagePath;
        if (n.EndsWith(".exe", StringComparison.OrdinalIgnoreCase)) n = n.Substring(0, n.Length - 4);
        return n;
    }

    /* ---------------- 生命周期 ---------------- */
    public static void Init()
    {
        Topo.Detect();
        DetectCpuSetApi();
        lock (_sync)
        {
            if (Cfg.FcRules.Count == 0) return;
            if (EnsureWatching()) StockCheck();
        }
    }

    public static void Shutdown()
    {
        lock (_sync)
        {
            _shutdown = true;   // 补写定时器见此标志直接放弃
            foreach (var pid in new List<int>(_eng.Keys)) Restore(pid);
            ReleaseWatch();
        }
    }

    public static void RuleAdded(string name, int core)
    {
        lock (_sync)
        {
            if (!EnsureWatching()) { Msg("首核调度：进程事件监听启动失败：" + EtwProc.Error); return; }
            ApplyByName(name, core, null);
        }
    }

    public static void RuleRemoved(string name)
    {
        bool idle;
        lock (_sync)
        {
            var gone = new List<int>();
            foreach (var kv in _eng) if (string.Equals(kv.Value.Name, name, StringComparison.OrdinalIgnoreCase)) gone.Add(kv.Key);
            foreach (var pid in gone) Restore(pid);
            lock (Cfg.FcRules) idle = Cfg.FcRules.Count == 0;
            if (idle) ReleaseWatch();
        }
    }

    // 核心变更：先比较还原再按新核心重钉
    public static void RuleChanged(string name, int core)
    {
        lock (_sync)
        {
            var hit = new List<int>();
            foreach (var kv in _eng) if (string.Equals(kv.Value.Name, name, StringComparison.OrdinalIgnoreCase)) hit.Add(kv.Key);
            foreach (var pid in hit) Restore(pid);
            if (EnsureWatching()) ApplyByName(name, core, null);
        }
    }

    static void ApplyByName(string name, int core, System.Text.StringBuilder log)
    {
        try
        {
            foreach (var p in Process.GetProcessesByName(name))
            {
                bool had = _eng.ContainsKey(p.Id);
                Apply(p.Id, name, core, log);
                if (!had) ArmStages(p.Id, name, core);   // 失败也排补写重试
                p.Dispose();
            }
        }
        catch { }
    }

    static void StockCheck()
    {
        List<KeyValuePair<string, int>> rules;
        lock (Cfg.FcRules) rules = new List<KeyValuePair<string, int>>(Cfg.FcRules);
        foreach (var kv in rules) ApplyByName(kv.Key, kv.Value, null);
    }

    /* ---------------- ETW 监听（与 Iso 共享会话） ---------------- */
    static bool EnsureWatching()
    {
        if (_watching) return true;
        if (!EtwProc.Acquire()) return false;
        if (!_subscribed) { EtwProc.Started += OnProcStart; EtwProc.Stopped += OnProcStop; _subscribed = true; }
        _watching = true;
        return true;
    }

    static void ReleaseWatch()
    {
        if (!_watching) return;
        _watching = false;
        EtwProc.Release();   // 订阅保留：会话重启后事件自然恢复，且不重复叠加
    }

    static DateTime _lastActiveSweep;
    public static void OnWindowActive()
    {
        lock (_sync)
        {
            if (_shutdown || (DateTime.Now - _lastActiveSweep).TotalSeconds < 5) return;
            _lastActiveSweep = DateTime.Now;
        }
        Task.Run(() => { lock (_sync) { if (!_shutdown) StockCheck(); } });
    }

    static void OnProcStart(int pid, string imagePath)
    {
        string name = FileName(imagePath);
        if (name.Length == 0) return;
        int core;
        lock (Cfg.FcRules) if (!Cfg.FcRules.TryGetValue(name, out core)) return;
        lock (_sync)
        {
            if (_shutdown) return;
            Apply(pid, name, core, null);
            ArmStages(pid, name, core);   // 失败也排补写：反作弊游戏启动早期可能暂时不可写，10s/30s 重试接住
        }
    }

    static void OnProcStop(int pid)
    {
        lock (_sync) _eng.Remove(pid);   // 进程死了设置随线程消亡，无需还原；补写定时器到点发现人已没自然放弃
    }

    /* ---------------- 核心：应用（首写与补写同路，恒硬模式；core=逻辑线程号） ---------------- */
    static bool Apply(int pid, string name, int core, System.Text.StringBuilder log)
    {
        Eng old;
        bool reapply = _eng.TryGetValue(pid, out old);
        if (!Topo.Supported || core < 0 || core >= Topo.LogicalCount) { Log(log, "FAIL: 拓扑不可用或逻辑核超范围"); return false; }
        if (!_cpuSetApi) { Msg("首核调度：系统无 CPU Sets API，功能不可用"); Log(log, "FAIL: no cpu set api"); return false; }
        // 前台区限制只约束前台规则进程：其他进程全核可选（软隔离按独立前台区）
        bool isoGame;
        lock (Cfg.IsoGames) isoGame = Cfg.IsoGames.Contains(name);
        ulong gamePool = Topo.AllMask;
        ulong isoMask, isoGameMask;
        Iso.Zones(out isoMask, out isoGameMask);
        if (isoGame) gamePool &= isoGameMask;
        if ((gamePool & (1UL << core)) == 0) { if (!reapply) Msg("首核调度：" + name + ".exe 首核 " + core + " 在隔离区内，未写入"); Log(log, "FAIL: 首核在隔离区"); return false; }
        // coreMask=首核所在物理核（仅用于梳理避让范围；钉死本身是精确单线程）
        ulong coreMask = 0;
        for (int i = 0; i < Topo.Cores.Count; i++) if ((Topo.Cores[i].Mask & (1UL << core)) != 0) { coreMask = Topo.Cores[i].Mask; break; }
        if (coreMask == 0) coreMask = 1UL << core;   // 兜底：找不到物理核就只避让自身

        if (!_seDebug) { SuiteApp.EnablePrivilege("SeDebugPrivilege"); _seDebug = true; }
        IntPtr hp = Native.OpenProcess(P_QLIMITED | P_VMREAD, false, pid);
        if (hp == IntPtr.Zero) { if (!reapply) Msg("首核调度：" + name + ".exe 受保护或无权访问，已跳过"); Log(log, "FAIL: OpenProcess " + Marshal.GetLastWin32Error()); return false; }
        try
        {
            long pc, pe, pk, pu;
            if (!Native.GetProcessTimes(hp, out pc, out pe, out pk, out pu)) { Log(log, "FAIL: GetProcessTimes"); return false; }
            DateTime start = DateTime.FromFileTimeUtc(pc);
            if (reapply && start != old.ProcStart) { _eng.Remove(pid); reapply = false; }   // PID 复用：按新进程重新接管

            uint tid; ulong tcreate;
            if (!FindMainThread(hp, pid, out tid, out tcreate, log))
            { if (!reapply) Msg("首核调度：" + name + ".exe 主线程识别失败，未做任何写入"); Log(log, "FAIL: main thread not found"); return false; }

            int n = core;
            uint[] pair = new uint[] { _cpuSetIds[n] };   // 钉死=精确首核单线程（选 5 就是 5）
            var ideal = new Native.PROCESSOR_NUMBER { Group = 0, Number = (byte)n };

            IntPtr th = Native.OpenThread(TH_SET | TH_QUERY, false, tid);
            if (th == IntPtr.Zero) { if (!reapply) Msg("首核调度：" + name + ".exe 线程句柄被拒（反作弊保护？），已跳过"); Log(log, "FAIL: OpenThread " + Marshal.GetLastWin32Error()); return false; }
            try
            {
                if (reapply && old.Tid == tid && old.ThreadCreate == tcreate)
                {
                    // 补写：主线程还是原来那个——快照不动，只把目标值重写一遍+重梳理
                    if (!SetsEqual(ReadSets(th), old.PairIds))
                        Native.SetThreadSelectedCpuSets(th, old.PairIds, (uint)old.PairIds.Length);   // 曾写死 2 越界：PairIds 仅 1 元素（钉单核）
                    Native.PROCESSOR_NUMBER ri0, prev0;
                    if (Native.GetThreadIdealProcessorEx(th, out ri0) && (ri0.Group != 0 || ri0.Number != old.Ideal.Number))
                        Native.SetThreadIdealProcessorEx(th, ref old.Ideal, out prev0);
                    int reSweep = Sweep(pid, tid, coreMask, gamePool, old.Swept, log);
                    Log(log, "补写 OK: tid=" + tid + " 梳理=" + reSweep);
                    return true;
                }
                if (reapply) Restore(pid);   // 主线程换人了：旧快照比较还原，再按新线程全新接管

                // 接管前快照（还原责任）
                uint[] origSets = ReadSets(th);
                if (origSets == null) { Log(log, "FAIL: 读原 CPU Sets"); return false; }
                Native.PROCESSOR_NUMBER origIdeal;
                if (!Native.GetThreadIdealProcessorEx(th, out origIdeal)) { Log(log, "FAIL: 读原 Ideal"); return false; }

                // 写前再验一次身份（D13：任何身份不可读/不匹配=零写）
                long c2, e2, k2, u2;
                if (!Native.GetProcessTimes(hp, out c2, out e2, out k2, out u2) || c2 != pc) { Log(log, "FAIL: 进程身份漂移"); return false; }
                if (!Native.GetThreadTimes(th, out c2, out e2, out k2, out u2) || (ulong)c2 != tcreate) { Log(log, "FAIL: 线程身份漂移"); return false; }

                // 先写 CPU Sets 再写 Ideal；每写必读回，失败回滚
                if (!Native.SetThreadSelectedCpuSets(th, pair, (uint)pair.Length)) { Log(log, "FAIL: SetCpuSets " + Marshal.GetLastWin32Error()); return false; }
                uint[] rb = ReadSets(th);
                if (!SetsEqual(rb, pair))
                {
                    Native.SetThreadSelectedCpuSets(th, origSets, (uint)origSets.Length);
                    Log(log, "FAIL: CPU Sets 读回不一致，已回滚");
                    return false;
                }
                Native.PROCESSOR_NUMBER prev;
                if (!Native.SetThreadIdealProcessorEx(th, ref ideal, out prev))
                {
                    Native.SetThreadSelectedCpuSets(th, origSets, (uint)origSets.Length);
                    Log(log, "FAIL: SetIdeal " + Marshal.GetLastWin32Error());
                    return false;
                }
                Native.PROCESSOR_NUMBER ri;
                if (!Native.GetThreadIdealProcessorEx(th, out ri) || ri.Number != ideal.Number || ri.Group != 0)
                {
                    Native.SetThreadSelectedCpuSets(th, origSets, (uint)origSets.Length);
                    Native.SetThreadIdealProcessorEx(th, ref origIdeal, out prev);
                    Log(log, "FAIL: Ideal 读回不一致，已回滚");
                    return false;
                }

                var eng = new Eng
                {
                    Name = name, ProcStart = start, Tid = tid, ThreadCreate = tcreate,
                    Core = core, Ideal = ideal, PairIds = pair,
                    OrigSets = origSets, OrigIdeal = origIdeal
                };
                _eng[pid] = eng;
                int moved = Sweep(pid, tid, coreMask, gamePool, eng.Swept, log);
                Msg("首核调度：" + name + ".exe 主线程 → " + core + (moved > 0 ? " · 梳理 " + moved + " 线程" : ""));
                Log(log, "OK: tid=" + tid + " ideal=" + n + " 钉死=单线程 梳理=" + moved);
                return true;
            }
            finally { Native.CloseHandle(th); }
        }
        finally { Native.CloseHandle(hp); }
    }

    // 主线程识别双路径：
    // ①模块范围可读 → "起始地址落 exe 主模块 + 创建最早"（高置信）
    // ②EnumProcessModules 被反作弊拒绝（err 5，游戏实测）→ 降级"创建最早"（线程0恒为全进程最先创建=OS 级主线程）
    public static bool FindMainThread(IntPtr hp, int pid, out uint tid, out ulong create100, System.Text.StringBuilder log)   // public：算法一复用
    {
        tid = 0; create100 = 0;
        long lo = 0, hi = 0;
        IntPtr[] mods = new IntPtr[1];
        uint need;
        if (Native.EnumProcessModules(hp, mods, (uint)IntPtr.Size, out need) && mods[0] != IntPtr.Zero)
        {
            Native.MODULEINFO mi;
            if (Native.GetModuleInformation(hp, mods[0], out mi, (uint)Marshal.SizeOf(typeof(Native.MODULEINFO))))
            { lo = mi.lpBaseOfDll.ToInt64(); hi = lo + mi.SizeOfImage; }
        }
        bool degraded = hi == 0;
        if (degraded) Log(log, "模块枚举被拒(err " + Marshal.GetLastWin32Error() + ")，降级按创建最早识别");

        IntPtr snap = Native.CreateToolhelp32Snapshot(4, (uint)pid);   // TH32CS_SNAPTHREAD
        if (snap == IntPtr.Zero || snap == Native.InvalidHandle) return false;
        try
        {
            var te = new Native.THREADENTRY32 { dwSize = (uint)Marshal.SizeOf(typeof(Native.THREADENTRY32)) };
            if (!Native.Thread32First(snap, ref te)) return false;
            uint bestTid = 0, bestModTid = 0;
            ulong bestC = ulong.MaxValue, bestModC = ulong.MaxValue;
            int inModule = 0;
            do
            {
                if (te.th32OwnerProcessID != (uint)pid) continue;
                // 必须 THREAD_QUERY_INFORMATION：ThreadQuerySetWin32StartAddress 不认 QUERY_LIMITED（0xC0000022，20348 实测）
                IntPtr th = Native.OpenThread(TH_QUERY, false, te.th32ThreadID);
                if (th == IntPtr.Zero) continue;
                try
                {
                    long c, e, k, u;
                    if (!Native.GetThreadTimes(th, out c, out e, out k, out u)) continue;
                    bool inMod = false;
                    IntPtr startAddr;
                    if (Native.NtQueryInformationThread(th, 9, out startAddr, IntPtr.Size, IntPtr.Zero) == 0)
                    {
                        long a = startAddr.ToInt64();
                        inMod = hi != 0 && a >= lo && a < hi;
                    }
                    if (inMod) inModule++;
                    if ((ulong)c < bestC) { bestC = (ulong)c; bestTid = te.th32ThreadID; }
                    if (inMod && (ulong)c < bestModC) { bestModC = (ulong)c; bestModTid = te.th32ThreadID; }
                }
                finally { Native.CloseHandle(th); }
            } while (Native.Thread32Next(snap, ref te));

            if (degraded) { tid = bestTid; create100 = bestC; }                    // 降级：创建最早
            else if (bestModTid != 0) { tid = bestModTid; create100 = bestModC; }  // 高置信：模块内最早
            else { Log(log, "主线程候选=0（无模块内线程），拒绝"); return false; }
            Log(log, "主线程 tid=" + tid + (degraded ? "（降级·创建最早）" : " 候选=" + inModule + (bestTid == bestModTid ? " 最早∈模块" : " 取模块内最早")));
            return true;
        }
        finally { Native.CloseHandle(snap); }
    }

    /* ---------------- 分阶段补写（一次性定时器链，到点即毁；零轮询） ---------------- */
    static void ArmStages(int pid, string name, int core) { ArmStage(pid, name, core, 0); }

    static void ArmStage(int pid, string name, int core, int stage)
    {
        if (stage >= StageMs.Length) return;
        System.Threading.Timer t = null;
        t = new System.Threading.Timer(_ =>
        {
            try { t.Dispose(); } catch { }
            try
            {
                lock (_sync)
                {
                    if (_shutdown) return;
                    // 规则被改/删过：后续阶段作废（RuleChanged 会自己重新武装）
                    int cur;
                    lock (Cfg.FcRules) if (!Cfg.FcRules.TryGetValue(name, out cur) || cur != core) return;
                    if (!PidAlive(pid)) return;   // 进程已死：放弃后续阶段
                    Apply(pid, name, cur, null);   // 成败都继续下一阶段（成功=补写，失败=重试）
                    ArmStage(pid, name, cur, stage + 1);
                }
            }
            catch { }
        }, null, StageMs[stage], Timeout.Infinite);
    }

    /* ---------------- 梳理：Ideal 落在首核物理核上的同进程其他线程 → 空闲核（单次写；池由调用方按进程算好） ---------------- */
    static int Sweep(int pid, uint mainTid, ulong coreMask, ulong gamePool, List<Swept> swept, System.Text.StringBuilder log)
    {
        ulong pool = gamePool & ~coreMask;              // 首核物理核整核留给主线程（SMT 兄弟共享执行单元）
        if (pool == 0) return 0;
        var cpus = new List<int>();
        for (int b = 0; b < Topo.LogicalCount; b++) if ((pool & (1UL << b)) != 0) cpus.Add(b);

        int moved = 0, rr = 0;
        IntPtr snap = Native.CreateToolhelp32Snapshot(4, (uint)pid);
        if (snap == IntPtr.Zero || snap == Native.InvalidHandle) return 0;
        try
        {
            var te = new Native.THREADENTRY32 { dwSize = (uint)Marshal.SizeOf(typeof(Native.THREADENTRY32)) };
            if (!Native.Thread32First(snap, ref te)) return 0;
            do
            {
                if (te.th32OwnerProcessID != (uint)pid || te.th32ThreadID == mainTid) continue;
                IntPtr th = Native.OpenThread(TH_SET | TH_QUERY, false, te.th32ThreadID);
                if (th == IntPtr.Zero) continue;
                try
                {
                    uint req;
                    uint[] probe = new uint[4];
                    if (!Native.GetThreadSelectedCpuSets(th, probe, (uint)probe.Length, out req)) continue;
                    if (req > 0) continue;                              // 第三方 CPU Sets：尊重不碰
                    Native.PROCESSOR_NUMBER cur;
                    if (!Native.GetThreadIdealProcessorEx(th, out cur)) continue;
                    if (cur.Group != 0 || (coreMask & (1UL << cur.Number)) == 0) continue;
                    bool known = false;
                    for (int i = 0; i < swept.Count; i++) if (swept[i].Tid == te.th32ThreadID) { known = true; break; }
                    long c = 0, e2, k, u;
                    if (!known && !Native.GetThreadTimes(th, out c, out e2, out k, out u)) continue;
                    var target = new Native.PROCESSOR_NUMBER { Group = 0, Number = (byte)cpus[rr % cpus.Count] };
                    rr++;
                    Native.PROCESSOR_NUMBER prev;
                    if (!Native.SetThreadIdealProcessorEx(th, ref target, out prev)) continue;
                    if (!known) swept.Add(new Swept { Tid = te.th32ThreadID, Create = (ulong)c, Orig = cur, Target = target });
                    moved++;
                }
                finally { Native.CloseHandle(th); }
            } while (Native.Thread32Next(snap, ref te));
        }
        finally { Native.CloseHandle(snap); }
        Log(log, "梳理 moved=" + moved);
        return moved;
    }

    /* ---------------- 还原（比较还原：仍是我们写的目标才动，第三方接管则尊重） ---------------- */
    static void Restore(int pid)
    {
        Eng e;
        if (!_eng.TryGetValue(pid, out e)) return;
        _eng.Remove(pid);
        IntPtr hp = Native.OpenProcess(P_QLIMITED, false, pid);
        if (hp == IntPtr.Zero) return;
        try
        {
            long c, x, k, u;
            if (!Native.GetProcessTimes(hp, out c, out x, out k, out u) || DateTime.FromFileTimeUtc(c) != e.ProcStart) return;
            IntPtr th = Native.OpenThread(TH_SET | TH_QUERY, false, e.Tid);
            if (th == IntPtr.Zero) return;
            try
            {
                if (!Native.GetThreadTimes(th, out c, out x, out k, out u) || (ulong)c != e.ThreadCreate) return;
                uint[] cur = ReadSets(th);
                if (SetsEqual(cur, e.PairIds))   // 只有仍是我们的目标才还原
                    Native.SetThreadSelectedCpuSets(th, e.OrigSets, (uint)e.OrigSets.Length);
                Native.PROCESSOR_NUMBER ri, prev;
                if (Native.GetThreadIdealProcessorEx(th, out ri) && ri.Number == e.Ideal.Number && ri.Group == e.Ideal.Group)
                    Native.SetThreadIdealProcessorEx(th, ref e.OrigIdeal, out prev);
                // 梳理线程同样比较还原（线程死了/第三方接管自然跳过）
                for (int i = 0; i < e.Swept.Count; i++)
                {
                    var sw = e.Swept[i];
                    IntPtr st = Native.OpenThread(TH_SET | TH_QUERY, false, sw.Tid);
                    if (st == IntPtr.Zero) continue;
                    try
                    {
                        long c3, x3, k3, u3;
                        if (!Native.GetThreadTimes(st, out c3, out x3, out k3, out u3) || (ulong)c3 != sw.Create) continue;
                        Native.PROCESSOR_NUMBER si, sprev;
                        if (Native.GetThreadIdealProcessorEx(st, out si) && si.Number == sw.Target.Number && si.Group == sw.Target.Group)
                            Native.SetThreadIdealProcessorEx(st, ref sw.Orig, out sprev);
                    }
                    finally { Native.CloseHandle(st); }
                }
            }
            finally { Native.CloseHandle(th); }
        }
        finally { Native.CloseHandle(hp); }
    }

    /* ---------------- CPU Set Id 映射（动态加载，老系统优雅降级软模式） ---------------- */
    public static void DetectCpuSetApi()   // public：算法一 CLI 路径复用
    {
        try
        {
            IntPtr k = Native.GetModuleHandle("kernel32.dll");
            IntPtr p = Native.GetProcAddress(k, "GetSystemCpuSetInformation");
            if (p == IntPtr.Zero || Topo.LogicalCount == 0) return;
            var fn = (Native.GetSysCpuSetInfo)Marshal.GetDelegateForFunctionPointer(p, typeof(Native.GetSysCpuSetInfo));
            uint len = 0;
            fn(IntPtr.Zero, 0, out len, IntPtr.Zero, 0);
            if (len == 0) return;
            IntPtr buf = Marshal.AllocHGlobal((int)len);
            try
            {
                uint got;
                if (!fn(buf, len, out got, IntPtr.Zero, 0)) return;
                var map = new uint[Topo.LogicalCount];
                var seen = new bool[Topo.LogicalCount];
                long off = 0;
                while (off < got)
                {
                    IntPtr cur = new IntPtr(buf.ToInt64() + off);
                    uint size = (uint)Marshal.ReadInt32(cur, 0);
                    if (size == 0) break;
                    if (Marshal.ReadInt32(cur, 4) == 0)   // Type=CpuSetInformation：Id@8 Group@12 LPIndex@14
                    {
                        int grp = Marshal.ReadInt16(cur, 12);
                        int lpi = Marshal.ReadByte(cur, 14);
                        if (grp == 0 && lpi >= 0 && lpi < Topo.LogicalCount) { map[lpi] = (uint)Marshal.ReadInt32(cur, 8); seen[lpi] = true; }
                    }
                    off += size;
                }
                for (int i = 0; i < Topo.LogicalCount; i++) if (!seen[i]) return;
                _cpuSetIds = map;
                _cpuSetApi = true;
            }
            finally { Marshal.FreeHGlobal(buf); }
        }
        catch { }
    }

    /* ---------------- 诊断：-fcapply <pid> <h|s><核>（应用→读回→还原，不持久化） ---------------- */
    public static int ApplyCli(string sPid, string mc)
    {
        Cfg.Load();   // CLI 路径不走 app.Init：隔离区校验要读 ISO_MASK，必须自己加载
        Topo.Detect();
        DetectCpuSetApi();
        var sb = new System.Text.StringBuilder();
        sb.AppendLine("topo: supported=" + Topo.Supported + " cores=" + Topo.Cores.Count + " logical=" + Topo.LogicalCount + " cpuSetApi=" + _cpuSetApi);
        int pid, core = -1;
        if (mc != null) int.TryParse(mc, out core);
        bool cliOk = false;
        if (core < 0 || !int.TryParse(sPid, out pid)) sb.AppendLine("usage: -fcapply <pid> <逻辑线程号>");
        else
        {
            string name = "pid" + pid;
            try { var pr = Process.GetProcessById(pid); name = pr.ProcessName; pr.Dispose(); } catch { }
            cliOk = Apply(pid, name, core, sb);
            sb.AppendLine(cliOk ? "APPLY OK" : "APPLY FAIL");
            if (cliOk)
            {
                System.Threading.Thread.Sleep(800);
                Restore(pid);
                sb.AppendLine("RESTORED");
            }
        }
        try { File.WriteAllText(Path.Combine(Path.GetTempPath(), "dunsuitelite_fc.txt"), sb.ToString()); } catch { }
        return cliOk ? 0 : 2;
    }

    /* ---------------- 小工具 ---------------- */
    static uint[] ReadSets(IntPtr th)
    {
        uint req;
        uint[] buf = new uint[128];
        if (!Native.GetThreadSelectedCpuSets(th, buf, (uint)buf.Length, out req)) return null;
        if (req > (uint)buf.Length)
        {
            buf = new uint[req];
            if (!Native.GetThreadSelectedCpuSets(th, buf, req, out req)) return null;
        }
        var r = new uint[req];
        Array.Copy(buf, r, (int)req);
        return r;
    }

    static bool SetsEqual(uint[] a, uint[] b)
    {
        if (a == null || b == null) return false;
        if (a.Length != b.Length) return false;
        var x = (uint[])a.Clone(); var y = (uint[])b.Clone();
        Array.Sort(x); Array.Sort(y);
        for (int i = 0; i < x.Length; i++) if (x[i] != y[i]) return false;
        return true;
    }

    static void Log(System.Text.StringBuilder sb, string s) { if (sb != null) sb.AppendLine(s); }
}

static class IrqIso
{
    static IrqIso() { IrqOriginalStore.Configure(Cfg.Dir); }

    public class Dev
    {
        public string Path;        // PCI\VEN_xxxx&DEV_xxxx\instance
        public string Label;       // 显卡/网卡/声卡/存储/USB（同类多个加序号；含输入设备的标 USB3(键鼠)）
        public string FullName;
        public string Hosts = "";  // 挂载的输入设备（鼠标、键盘…），空=无
        public int Msi = -1;       // -1 未知 0 关 1 开
        public bool Isolated;      // DevicePolicy=4 且掩码==当前中断落点（EffectiveMask）
        public bool Custom;        // DevicePolicy=4 但掩码不同（第三方指定）
    }

    // 中断落点掩码：custom 模式用自选 IRQ_MASK，否则跟随当前模式隔离区（follow/缺省，老行为）
    public static ulong EffectiveMask()
    {
        ulong iso, game;
        Iso.Zones(out iso, out game);
        return Cfg.IrqMode == "custom" && Cfg.IrqMask != 0 ? Cfg.IrqMask & Topo.AllMask : iso;
    }

    [DllImport("cfgmgr32.dll", CharSet = CharSet.Unicode)]
    static extern int CM_Locate_DevNodeW(out int devInst, string id, int flags);
    [DllImport("cfgmgr32.dll")]
    static extern int CM_Get_Parent(out int parent, int devInst, int flags);
    [DllImport("cfgmgr32.dll", CharSet = CharSet.Unicode)]
    static extern int CM_Get_Device_IDW(int devInst, System.Text.StringBuilder id, int len, int flags);

    const string GUID_MOUSE = "{4d36e96f-e325-11ce-bfc1-08002be10318}";
    const string GUID_KEYBOARD = "{4d36e96b-e325-11ce-bfc1-08002be10318}";
    const string GUID_MEDIA = "{4d36e96c-e325-11ce-bfc1-08002be10318}";

    // 输入设备宿主识别：枚举 Enum\HID/Enum\USB 的鼠标/键盘/音频/手柄设备，沿 PNP 父链爬回 PCI 控制器
    static Dictionary<string, List<string>> MapInputDevices()
    {
        var map = new Dictionary<string, List<string>>(StringComparer.OrdinalIgnoreCase);
        foreach (var root in new[] { "HID", "USB" })
        {
            using (var rk = Microsoft.Win32.Registry.LocalMachine.OpenSubKey(@"SYSTEM\CurrentControlSet\Enum\" + root))
            {
                if (rk == null) continue;
                foreach (var dev in rk.GetSubKeyNames())
                {
                    string[] insts;
                    try { using (var dk = rk.OpenSubKey(dev)) { if (dk == null) continue; insts = dk.GetSubKeyNames(); } }
                    catch { continue; }
                    foreach (var inst in insts)
                    {
                        try
                        {
                            using (var ik = rk.OpenSubKey(dev + "\\" + inst))
                            {
                                if (ik == null) continue;
                                string guid = ik.GetValue("ClassGuid") as string;
                                string name = (ik.GetValue("FriendlyName") as string ?? ik.GetValue("DeviceDesc") as string ?? "").ToLowerInvariant();
                                string kind = null;
                                if (guid != null && guid.Equals(GUID_MOUSE, StringComparison.OrdinalIgnoreCase)) kind = "鼠标";
                                else if (guid != null && guid.Equals(GUID_KEYBOARD, StringComparison.OrdinalIgnoreCase)) kind = "键盘";
                                else if (guid != null && guid.Equals(GUID_MEDIA, StringComparison.OrdinalIgnoreCase)) kind = "音频";
                                else if (name.Contains("xbox") || name.Contains("gamepad") || name.Contains("controller") || name.Contains("手柄")) kind = "手柄";
                                if (kind == null) continue;
                                string pci = FindPciParent(root + "\\" + dev + "\\" + inst);
                                if (pci == null) continue;
                                List<string> l;
                                if (!map.TryGetValue(pci, out l)) { l = new List<string>(); map[pci] = l; }
                                if (!l.Contains(kind)) l.Add(kind);
                            }
                        }
                        catch { }
                    }
                }
            }
        }
        return map;
    }

    static string FindPciParent(string instancePath)
    {
        int dev;
        if (CM_Locate_DevNodeW(out dev, instancePath, 0) != 0) return null;
        for (int depth = 0; depth < 12; depth++)
        {
            int parent;
            if (CM_Get_Parent(out parent, dev, 0) != 0) return null;
            dev = parent;
            var sb = new System.Text.StringBuilder(512);
            if (CM_Get_Device_IDW(dev, sb, sb.Capacity, 0) != 0) return null;
            string id = sb.ToString();
            if (id.StartsWith("PCI\\", StringComparison.OrdinalIgnoreCase)) return id;
        }
        return null;
    }

    // 本机（修改版系统）实例键只有 ClassGUID 没有 Class 名——按 GUID 匹配（devguid.h 标准类），Class 名做回退
    static readonly Dictionary<string, string> _classLabel = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase)
    {
        { "{4d36e968-e325-11ce-bfc1-08002be10318}", "显卡" },   // DISPLAY
        { "{4d36e972-e325-11ce-bfc1-08002be10318}", "网卡" },   // NET
        { "{4d36e96c-e325-11ce-bfc1-08002be10318}", "声卡" },   // MEDIA
        { "{36fc9e60-c465-11cf-8056-444553540000}", "USB" },    // USB
        { "{4d36e96a-e325-11ce-bfc1-08002be10318}", "存储" },   // HDC
        { "{4d36e97b-e325-11ce-bfc1-08002be10318}", "存储" },   // SCSIAdapter
    };
    static readonly Dictionary<string, string> _classNameLabel = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase)
    {
        { "Display", "显卡" }, { "Net", "网卡" }, { "Media", "声卡" },
        { "USB", "USB" }, { "HDC", "存储" }, { "SCSIAdapter", "存储" }
    };
    static readonly string[] _virtualBlack = { "todesk", "parsec", "iddcx", "usb display", "virtual", "microsoft basic" };

    public static List<Dev> EnumDevices(ulong isoMask)
    {
        var list = new List<Dev>();
        using (var pci = Microsoft.Win32.Registry.LocalMachine.OpenSubKey(@"SYSTEM\CurrentControlSet\Enum\PCI"))
        {
            if (pci == null) return list;
            foreach (var ven in pci.GetSubKeyNames())
            {
                string[] insts;
                try { using (var venKey = pci.OpenSubKey(ven)) { if (venKey == null) continue; insts = venKey.GetSubKeyNames(); } }
                catch { continue; }   // 单个权限怪键不拖垮整个枚举
                foreach (var inst in insts)
                {
                    try
                    {
                        Dev d = null;
                        using (var dk = pci.OpenSubKey(ven + "\\" + inst))
                        {
                            if (dk == null) continue;
                            string label = null;
                            string cls = dk.GetValue("Class") as string;
                            if (cls != null) _classNameLabel.TryGetValue(cls, out label);
                            if (label == null)
                            {
                                string guid = dk.GetValue("ClassGuid") as string;
                                if (guid != null) _classLabel.TryGetValue(guid, out label);
                            }
                            if (label == null) continue;
                            string name = dk.GetValue("FriendlyName") as string ?? dk.GetValue("DeviceDesc") as string ?? "";
                            string low = name.ToLowerInvariant();
                            bool black = false;
                            foreach (var b in _virtualBlack) if (low.Contains(b)) { black = true; break; }
                            if (black) continue;
                            d = new Dev { Path = @"PCI\" + ven + "\\" + inst, Label = label, FullName = name };
                        }
                        Refresh(d, isoMask);
                        list.Add(d);
                    }
                    catch { }
                }
            }
        }
        var seen = new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase);
        foreach (var d in list)
        {
            int n;
            seen.TryGetValue(d.Label, out n);
            seen[d.Label] = n + 1;
            if (n > 0) d.Label = d.Label + (n + 1);   // 网卡 / 网卡2 …
        }
        var inputMap = MapInputDevices();   // 输入设备宿主标注：USB3(鼠标键盘)
        foreach (var d in list)
        {
            List<string> kids;
            if (d.Label.StartsWith("USB") && inputMap.TryGetValue(d.Path, out kids) && kids.Count > 0)
            {
                d.Hosts = string.Join("、", kids);
                d.Label = d.Label + "(" + d.Hosts.Replace("、", "") + ")";
            }
        }
        return list;
    }

    public static void Refresh(Dev d, ulong isoMask)
    {
        d.Isolated = false; d.Custom = false;
        try
        {
            using (var k = Microsoft.Win32.Registry.LocalMachine.OpenSubKey(PolicySub(d.Path)))
            {
                if (k == null) return;
                object pol = k.GetValue("DevicePolicy");
                byte[] ovr = k.GetValue("AssignmentSetOverride") as byte[];
                if (pol is int && (int)pol == 4 && ovr != null)
                {
                    ulong m = 0;
                    for (int i = 0; i < 8 && i < ovr.Length; i++) m |= (ulong)ovr[i] << (8 * i);
                    if (m == (isoMask & Topo.AllMask) && m != 0) d.Isolated = true;
                    else d.Custom = true;
                }
            }
            using (var k2 = Microsoft.Win32.Registry.LocalMachine.OpenSubKey(
                @"SYSTEM\CurrentControlSet\Enum\" + d.Path + @"\Device Parameters\Interrupt Management\MessageSignaledInterruptProperties"))
            {
                if (k2 != null) { object m = k2.GetValue("MSISupported"); if (m is int) d.Msi = (int)m; }
            }
        }
        catch { }
    }

    static string PolicySub(string devPath)
    {
        return @"SYSTEM\CurrentControlSet\Enum\" + devPath + @"\Device Parameters\Interrupt Management\Affinity Policy";
    }

    public static string SetIsolated(Dev d, bool on, ulong isoMask)
    {
        if (on && (isoMask & Topo.AllMask) == 0) return "先勾选隔离区核心再设中断";
        try { WriteState(d.Path, on, isoMask); }
        catch (UnauthorizedAccessException)
        {
            try { TakeOwnership(PolicySub(d.Path)); WriteState(d.Path, on, isoMask); }
            catch (Exception ex) { return "写入失败: " + ex.Message; }
        }
        catch (Exception ex) { return "写入失败: " + ex.Message; }
        return on ? d.Label + " 中断已写入隔离区，重启后生效" : d.Label + " 中断已恢复原值，重启后生效";
    }

    static void WriteState(string devPath, bool on, ulong isoMask)
    {
        if (!on)
        {
            if (IrqOriginalStore.Restore(devPath)) return;
            using (var legacy = Microsoft.Win32.Registry.LocalMachine.CreateSubKey(PolicySub(devPath), true))
            {
                legacy.DeleteValue("DevicePolicy", false);
                legacy.DeleteValue("AssignmentSetOverride", false);
            }
            return;
        }
        IrqOriginalStore.Capture(devPath);
        try
        {
            using (var k = Microsoft.Win32.Registry.LocalMachine.CreateSubKey(PolicySub(devPath), true))
            {
                k.SetValue("DevicePolicy", 4, Microsoft.Win32.RegistryValueKind.DWord);
                k.SetValue("AssignmentSetOverride", BitConverter.GetBytes(isoMask & Topo.AllMask), Microsoft.Win32.RegistryValueKind.Binary);
                object policy = k.GetValue("DevicePolicy");
                byte[] assignment = k.GetValue("AssignmentSetOverride") as byte[];
                ulong actual = 0;
                if (assignment != null) for (int i = 0; i < 8 && i < assignment.Length; i++) actual |= (ulong)assignment[i] << (8 * i);
                if (!(policy is int) || (int)policy != 4 || actual != (isoMask & Topo.AllMask))
                    throw new InvalidOperationException("IRQ 写后读回不一致");
            }
        }
        catch
        {
            IrqOriginalStore.Restore(devPath);
            throw;
        }
    }

    // Enum 键夺权：从设备键逐级向下，所有者改 Administrators + 授 FullControl（仅写失败时调用）
    static void TakeOwnership(string relSub)
    {
        SuiteApp.EnablePrivilege("SeTakeOwnershipPrivilege");
        string cur = "";
        foreach (var seg in relSub.Split('\\'))
        {
            cur = cur.Length == 0 ? seg : cur + "\\" + seg;
            try
            {
                using (var k = Microsoft.Win32.Registry.LocalMachine.OpenSubKey(cur,
                    Microsoft.Win32.RegistryKeyPermissionCheck.ReadWriteSubTree, System.Security.AccessControl.RegistryRights.TakeOwnership))
                {
                    if (k != null)
                    {
                        var sec = k.GetAccessControl();
                        sec.SetOwner(new System.Security.Principal.NTAccount("Administrators"));
                        k.SetAccessControl(sec);
                    }
                }
                using (var k2 = Microsoft.Win32.Registry.LocalMachine.OpenSubKey(cur,
                    Microsoft.Win32.RegistryKeyPermissionCheck.ReadWriteSubTree, System.Security.AccessControl.RegistryRights.ChangePermissions))
                {
                    if (k2 != null)
                    {
                        var sec2 = k2.GetAccessControl();
                        sec2.AddAccessRule(new System.Security.AccessControl.RegistryAccessRule(
                            "Administrators", System.Security.AccessControl.RegistryRights.FullControl,
                            System.Security.AccessControl.AccessControlType.Allow));
                        k2.SetAccessControl(sec2);
                    }
                }
            }
            catch { }
        }
    }

    // 隔离区掩码变更时：掩码==旧隔离区的设备（我们写的）跟随改新区；第三方自定义掩码不动
    public static void Resync(ulong oldMask, ulong newMask)
    {
        if (newMask == 0 || oldMask == newMask) return;
        foreach (var d in EnumDevices(oldMask))
            if (d.Isolated) SetIsolated(d, true, newMask);
    }
}

