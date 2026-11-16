using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using Microsoft.Win32;

namespace DunSuiteLite.Scheduling
{
    public sealed class IrqOriginalSnapshot
    {
        public string RegistryPath = "";
        public bool HadKey;
        public bool HadDevicePolicy;
        public int DevicePolicy;
        public bool HadAssignment;
        public byte[] Assignment = new byte[0];
    }

    public static class IrqOriginalStore
    {
        private static readonly object Sync = new object();
        private static string StorePath;
        private static string _enumRoot = @"SYSTEM\CurrentControlSet\Enum\";

        public static void Configure(string directory)
        {
            lock (Sync) StorePath = Path.Combine(directory, "irq_originals.dat");
        }

        public static void ConfigureRootForTest(string enumRoot)
        {
            lock (Sync) _enumRoot = enumRoot;
        }

        public static IrqOriginalSnapshot Capture(string registryPath)
        {
            lock (Sync)
            {
                var existing = FindLocked(registryPath);
                if (existing != null) return existing;
                string sub = SubKey(registryPath);
                var snapshot = new IrqOriginalSnapshot { RegistryPath = registryPath };
                using (var key = Registry.LocalMachine.OpenSubKey(sub, false))
                {
                    snapshot.HadKey = key != null;
                    if (key != null)
                    {
                        object policy = key.GetValue("DevicePolicy", null, RegistryValueOptions.DoNotExpandEnvironmentNames);
                        if (policy != null)
                        {
                            if (!(policy is int)) throw new InvalidDataException("DevicePolicy 类型不是 DWORD，已中止 IRQ 写入");
                            snapshot.HadDevicePolicy = true;
                            snapshot.DevicePolicy = (int)policy;
                        }
                        object assignment = key.GetValue("AssignmentSetOverride", null, RegistryValueOptions.DoNotExpandEnvironmentNames);
                        if (assignment != null)
                        {
                            if (!(assignment is byte[])) throw new InvalidDataException("AssignmentSetOverride 类型不是 BINARY，已中止 IRQ 写入");
                            snapshot.HadAssignment = true;
                            snapshot.Assignment = (byte[])assignment;
                        }
                    }
                }
                var snapshots = LoadLocked();
                snapshots[registryPath] = snapshot;
                SaveLocked(snapshots);
                return snapshot;
            }
        }

        public static IrqOriginalSnapshot Find(string registryPath)
        {
            lock (Sync) return FindLocked(registryPath);
        }

        public static bool Restore(string registryPath)
        {
            lock (Sync)
            {
                var snapshots = LoadLocked();
                IrqOriginalSnapshot snapshot;
                if (!snapshots.TryGetValue(registryPath, out snapshot)) return false;
                string sub = SubKey(registryPath);
                using (var key = Registry.LocalMachine.CreateSubKey(sub, true))
                {
                    if (snapshot.HadDevicePolicy) key.SetValue("DevicePolicy", snapshot.DevicePolicy, RegistryValueKind.DWord);
                    else key.DeleteValue("DevicePolicy", false);
                    if (snapshot.HadAssignment) key.SetValue("AssignmentSetOverride", snapshot.Assignment, RegistryValueKind.Binary);
                    else key.DeleteValue("AssignmentSetOverride", false);
                    object policy = key.GetValue("DevicePolicy");
                    byte[] assignment = key.GetValue("AssignmentSetOverride") as byte[];
                    if (snapshot.HadDevicePolicy && (!(policy is int) || (int)policy != snapshot.DevicePolicy) ||
                        !snapshot.HadDevicePolicy && policy != null)
                        throw new InvalidOperationException("IRQ DevicePolicy 还原读回不一致");
                    if (!BytesEqual(assignment, snapshot.HadAssignment ? snapshot.Assignment : null))
                        throw new InvalidOperationException("IRQ AssignmentSetOverride 还原读回不一致");
                }
                if (!snapshot.HadKey) DeleteKeyIfEmpty(sub);
                snapshots.Remove(registryPath);
                SaveLocked(snapshots);
                return true;
            }
        }

        private static IrqOriginalSnapshot FindLocked(string registryPath)
        {
            IrqOriginalSnapshot snapshot;
            return LoadLocked().TryGetValue(registryPath, out snapshot) ? snapshot : null;
        }

        private static Dictionary<string, IrqOriginalSnapshot> LoadLocked()
        {
            var result = new Dictionary<string, IrqOriginalSnapshot>(StringComparer.OrdinalIgnoreCase);
            if (string.IsNullOrEmpty(StorePath) || !File.Exists(StorePath)) return result;
            foreach (string line in File.ReadAllLines(StorePath, Encoding.ASCII))
            {
                if (line.Length == 0) continue;
                string[] parts = line.Split('|');
                if (parts.Length != 6) continue;
                var snapshot = new IrqOriginalSnapshot
                {
                    RegistryPath = Encoding.UTF8.GetString(Convert.FromBase64String(parts[0])),
                    HadKey = parts[1] == "1",
                    HadDevicePolicy = parts[2] == "1",
                    DevicePolicy = ParseInt(parts[3]),
                    HadAssignment = parts[4] == "1",
                    Assignment = Convert.FromBase64String(parts[5])
                };
                result[snapshot.RegistryPath] = snapshot;
            }
            return result;
        }

        private static void SaveLocked(Dictionary<string, IrqOriginalSnapshot> snapshots)
        {
            if (string.IsNullOrEmpty(StorePath)) throw new InvalidOperationException("IRQ 原值存储路径未配置");
            Directory.CreateDirectory(Path.GetDirectoryName(StorePath));
            var lines = new List<string>();
            foreach (var pair in snapshots)
            {
                var s = pair.Value;
                lines.Add(Convert.ToBase64String(Encoding.UTF8.GetBytes(s.RegistryPath)) + "|" +
                    (s.HadKey ? "1" : "0") + "|" + (s.HadDevicePolicy ? "1" : "0") + "|" +
                    s.DevicePolicy.ToString(System.Globalization.CultureInfo.InvariantCulture) + "|" +
                    (s.HadAssignment ? "1" : "0") + "|" + Convert.ToBase64String(s.Assignment ?? new byte[0]));
            }
            string temporary = StorePath + ".tmp";
            File.WriteAllLines(temporary, lines.ToArray(), Encoding.ASCII);
            if (File.Exists(StorePath)) File.Replace(temporary, StorePath, null);
            else File.Move(temporary, StorePath);
        }

        private static bool BytesEqual(byte[] actual, byte[] expected)
        {
            if (expected == null || expected.Length == 0) return actual == null || actual.Length == 0;
            if (actual == null || actual.Length != expected.Length) return false;
            for (int i = 0; i < actual.Length; i++) if (actual[i] != expected[i]) return false;
            return true;
        }

        private static int ParseInt(string text)
        {
            int value;
            return int.TryParse(text, System.Globalization.NumberStyles.Integer,
                System.Globalization.CultureInfo.InvariantCulture, out value) ? value : 0;
        }

        private static string SubKey(string registryPath)
        {
            return _enumRoot + registryPath + @"\Device Parameters\Interrupt Management\Affinity Policy";
        }

        private static void DeleteKeyIfEmpty(string sub)
        {
            int split = sub.LastIndexOf('\\');
            if (split <= 0) return;
            string parentPath = sub.Substring(0, split);
            string child = sub.Substring(split + 1);
            using (var parent = Registry.LocalMachine.OpenSubKey(parentPath, true))
            {
                if (parent == null) return;
                using (var key = parent.OpenSubKey(child, false))
                    if (key != null && (key.ValueCount != 0 || key.SubKeyCount != 0)) return;
                parent.DeleteSubKey(child, false);
            }
        }
    }
}
