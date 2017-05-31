/* Shared */
var monthArray = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec']

/* Main stats page */
var rawDataIsLoading = false
var statusPagePassword = false

// Raw data updating
var minUpdateDelay = 1000 // Minimum delay between updates (in ms).
var lastRawUpdateTime = new Date()

/*
 * Workers
 */

function addhashtable(mainWorkerHash, workerHash) {
    var hashrow = `
    <div id="hashrow_${workerHash}" class="status_row">
      <div id="key_${workerHash}" class="status_cell"/>
      <div id="maximum_${workerHash}" class="status_cell"/>
      <div id="remaining_${workerHash}" class="status_cell"/>
      <div id="peak_${workerHash}" class="status_cell"/>
      <div id="expires_${workerHash}" class="status_cell"/>
      <div id="last_updated_${workerHash}" class="status_cell"/>
    </div>
    `
    $(hashrow).appendTo('#hashtable_' + mainWorkerHash)
}

function processHash(i, hashkey) {
    var hash = hashFnv32a(hashkey['key'], true)
    var mainHashHash
    mainHashHash = 'global'
    if ($('#hashtable_global').length === 0) {
        addhash('global')
    }

    if ($('#hashrow_' + hash).length === 0) {
        addhashtable(mainHashHash, hash)
    }

    var lastModified = new Date(hashkey['last_updated'])
    lastModified = lastModified.getHours() + ':' +
        ('0' + lastModified.getMinutes()).slice(-2) + ':' +
        ('0' + lastModified.getSeconds()).slice(-2) + ' ' +
        lastModified.getDate() + ' ' +
        monthArray[lastModified.getMonth()] + ' ' +
        lastModified.getFullYear()


    var expires = new Date(hashkey['expires'])
    expires = expires.getHours() + ':' +
        ('0' + expires.getMinutes()).slice(-2) + ':' +
        ('0' + expires.getSeconds()).slice(-2) + ' ' +
        expires.getDate() + ' ' +
        monthArray[expires.getMonth()] + ' ' +
        expires.getFullYear()

    $('#key_' + hash).html(hashkey['key'])
    $('#maximum_' + hash).html(hashkey['maximum'])
    $('#remaining_' + hash).html(hashkey['remaining'])
    $('#peak_' + hash).html(hashkey['peak'])
    $('#last_updated_' + hash).html(lastModified)
    $('#expires_' + hash).html(expires)
}

function parseResult(result) {
    $.each(result.HashKeys, processHash)
}

/*
 * Tables
 */
function addhash(hash) {
    var hashtable = `
    <div class="status_table" id="hashtable_${hash}">
     <div class="status_row header">
     <div class="status_cell">
       Hash Keys
      </div>
      <div class="status_cell">
        Maximum RPM
      </div>
      <div class="status_cell">
        RPM Left
        </div>
      <div class="status_cell">
        Peak
        </div>
       <div class="status_cell">
         Expires at
       </div>
       <div class="status_cell">
         Last Modified
       </div>
     </div>
   </div>`

    $('#status_container').prepend(hashtable)
    $(hashtable).find('.status_row.header .status_cell').click(hashtableSort)
}

function hashtableSort() {
    var hashtable = $(this).parents('.status_table').eq(0)
    var hashrow = hashtable.find('.status_row:gt(0)').toArray().sort(comparehash($(this).index()))
    this.asc = !this.asc
    if (!this.asc) {
        hashrow = hashrow.reverse()
    }
    for (var i = 0; i < hashrow.length; i++) {
        hashtable.append(hashrow[i])
    }
}

function getHashtableValue(hashrow, index) {
    return $(hashrow).children('.status_cell').eq(index).html()
}

function comparehash(index) {
    return function (a, b) {
        var valA = getHashtableValue(a, index)
        var valB = getHashtableValue(b, index)
        return $.isNumeric(valA) && $.isNumeric(valB) ? valA - valB : valA.localeCompare(valB)
    }
}

function updateStatus() {
    loadRawData().done(function (result) {
        // Parse result on success.
        parseResult(result)
    }).always(function () {
        // Only queue next request when previous is over.
        // Minimum delay of minUpdateDelay.
        var diff = new Date() - lastRawUpdateTime
        var delay = Math.max(minUpdateDelay - diff, 1) // Don't go below 1.

        // Don't use interval.
        window.setTimeout(updateStatus, delay)
    })
}

/**
 * Calculate a 32 bit FNV-1a hash
 * Found here: https://gist.github.com/vaiorabbit/5657561
 * Ref.: http://isthe.com/chongo/tech/comp/fnv/
 *
 * @param {string} str the input value
 * @param {boolean} [asString=false] set to true to return the hash value as
 *     8-digit hex string instead of an integer
 * @param {integer} [seed] optionally pass the hash of the previous chunk
 * @returns {integer | string}
 */
function hashFnv32a(str, asString, seed) {
    /* jshint bitwise:false */
    var i
    var l
    var hval = (seed === undefined) ? 0x811c9dc5 : seed

    for (i = 0, l = str.length; i < l; i++) {
        hval ^= str.charCodeAt(i)
        hval += (hval << 1) + (hval << 4) + (hval << 7) + (hval << 8) + (hval << 24)
    }

    if (asString) {
        // Convert to 8 digit hex string
        return ('0000000' + (hval >>> 0).toString(16)).substr(-8)
    }
    return hval >>> 0
}

function loadRawData() {
    return $.ajax({
        url: 'hashkeys',
        type: 'post',
        data: {
            'password': statusPagePassword
        },
        dataType: 'json',
        beforeSend: function () {
            if (rawDataIsLoading) {
                return false
            } else {
                rawDataIsLoading = true
            }
        },
        complete: function () {
            rawDataIsLoading = false
        }
    })
}


/*
 * Document ready
 */
$(document).ready(function () {
    // Set focus on password field.
    $('#password').focus()

    // Register to events.
    $('#password_form').submit(function (event) {
        event.preventDefault()

        statusPagePassword = $('#password').val()

        loadRawData().done(function (result) {
            if (result.login === 'ok') {
                $('.status_form').remove()
                parseResult(result)
                window.setTimeout(updateStatus, minUpdateDelay)
            } else {
                $('.status_form').effect('bounce')
                $('#password').focus()
            }
        })
    })
})
