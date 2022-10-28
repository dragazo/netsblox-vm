(function () {
    const SERVER = 'http://{{addr}}:{{port}}';

    function TerminalMorph(ext) {
        this.init();
        this.ext = ext;
    }
    TerminalMorph.prototype = new DialogBoxMorph();
    TerminalMorph.prototype.constructor = TerminalMorph;
    TerminalMorph.uber = DialogBoxMorph.prototype;
    TerminalMorph.instance = null;

    TerminalMorph.prototype.init = function() {
        TerminalMorph.uber.init.call(this);

        this.labelString = 'Native Terminal';
        this.createLabel();

        this.minWidth = 500;
        this.minHeight = 400;
        this.titleOffset = 5;
        this.padding = 20;

        this.bounds.setWidth(this.minWidth);
        this.bounds.setHeight(this.minHeight);

        this.handle = new HandleMorph(this, this.minWidth, this.minHeight, this.corner, this.corner);

        this.add(this.leftTools = new AlignmentMorph('row'));
        this.add(this.rightTools = new AlignmentMorph('row'));

        function makeSpacer(width) {
            const res = new Morph();
            res.setWidth(width);
            res.setHeight(1);
            res.alpha = 0;
            return res;
        }

        this.leftTools.add(this.runButton = new PushButtonMorph(null, async () => {
            const req = new XMLHttpRequest();
            req.onreadystatechange = () => {
                if (req.readyState !== XMLHttpRequest.DONE) return;
                if (req.status !== 200) {
                    alert(req.responseText);
                }
            };
            req.open('POST', `${SERVER}/run`, true);
            req.send(await this.ext.ide.cloud.exportRole());
        }, 'Run'));

        this.leftTools.add(makeSpacer(10));

        this.leftTools.add(this.stopButton = new PushButtonMorph(null, () => {
            console.log('stop pressed');

            const req = new XMLHttpRequest();
            req.onreadystatechange = () => {
                if (req.readyState !== XMLHttpRequest.DONE) return;
                console.log(req.responseText);
            };
            req.open('GET', `${SERVER}/output`, true);
            req.send(null);

        }, 'Stop'));

        this.rightTools.add(this.closeButton = new PushButtonMorph(null, () => {
            this.hide();
        }, 'Close'));

        this.fixLayout();
    };

    TerminalMorph.prototype.fixLayout = function () {
        if (this.leftTools) {
            this.leftTools.fixLayout();
            this.leftTools.setBottom(this.bottom() - this.padding);
            this.leftTools.setLeft(this.left() + this.padding);
        }

        if (this.rightTools) {
            this.rightTools.fixLayout();
            this.rightTools.setBottom(this.bottom() - this.padding);
            this.rightTools.setRight(this.right() - this.padding - this.handle.width());
        }

        if (this.label) {
            this.label.setCenter(this.center());
            this.label.setTop(this.top() + this.titleOffset);
        }
    };

    class NativeExtension extends Extension {
        constructor(ide) {
            super('Native');
            this.ide = ide;
        }

        onOpenRole() {}

        getMenu() {
            return {
                'Open Terminal': () => {
                    if (!TerminalMorph.instance) {
                        TerminalMorph.instance = new TerminalMorph(this);
                        TerminalMorph.instance.popUp(world);
                    } else {
                        TerminalMorph.instance.show();
                    }
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
                new Extension.Palette.Block('nativeSyscallError'),
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
                new Extension.Block('nativeSyscallError', 'reporter', 'native', 'error', [], fail),
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
