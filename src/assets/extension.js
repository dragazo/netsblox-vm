(function () {
    class NativeExtension extends Extension {
        constructor(ide) {
            super('Native');
            this.ide = ide;
        }

        onOpenRole() {}

        getMenu() {
            return {
                'Run on Device': async () => {
                    const req = new XMLHttpRequest();
                    req.open('POST', 'http://{{addr}}:{{port}}/run', true);
                    req.send(await this.ide.cloud.exportRole());
                },
            };
        }

        getCategories() {
            return [
                new Extension.Category('native', new Color(160, 20, 20)),
            ];
        }

        getPalette() {
            const blocks = [
                new Extension.Palette.Block('nativeRunSyscall'),
                new Extension.Palette.Block('nativeCallSyscall'),
            ];
            return [
                new Extension.PaletteCategory('native', blocks, SpriteMorph),
                new Extension.PaletteCategory('native', blocks, StageMorph),
            ];
        }

        getBlocks() {
            const fail = () => {
                throw Error("syscalls can't be used in the browser! run on native hardware!");
            };
            return [
                new Extension.Block('nativeRunSyscall', 'command', 'native', 'syscall %syscall %exp', [], fail),
                new Extension.Block('nativeCallSyscall', 'reporter', 'native', 'syscall %syscall %exp', [], fail),
            ];
        }

        getLabelParts() {
            return [
                new Extension.LabelPart('syscall', () => new InputSlotMorph(
                    null, // text
                    false, // numeric
                    {{syscalls}},
                    true, // readonly
                )),
            ];
        }
    }

    NetsBloxExtensions.register(NativeExtension);
})();
